\begin{code}
module Generic.Syntax where

open import Size
open import Data.Bool
open import Data.List.All
open import Data.List.Base as L hiding ([_])
open import Data.Product as P hiding (,_)
open import Function hiding (case_of_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import var
open import indexed 
open import environment as E hiding (traverse)

-- Descriptions and their Interpretation

\end{code}
%<*desc>
\begin{code}
data Desc (I : Set) : Set₁ where
  `σ : (A : Set) → (A → Desc I)  → Desc I
  `X : List I → I → Desc I       → Desc I
  `∎ : I                         → Desc I
\end{code}
%</desc>
%<*interp>
\begin{code}
⟦_⟧ : {I : Set} → Desc I → (List I → I ─Scoped) → I ─Scoped
⟦ `σ A d    ⟧ X i Γ = Σ[ a ∈ A ] (⟦ d a ⟧ X i Γ)
⟦ `X Δ j d  ⟧ X i Γ = X Δ j Γ × ⟦ d ⟧ X i Γ
⟦ `∎ i′     ⟧ X i Γ = i ≡ i′
\end{code}
%</interp>

\begin{code}
-- Syntaxes: Free Relative Monad of a Description's Interpretation
\end{code}
%<*scope>
\begin{code}
Scope :  {I : Set} (T : I ─Scoped) →
         (List I → I ─Scoped)
Scope T Δ i = (Δ ++_) ⊢ T i
\end{code}
%</scope>
%<*mu>
\begin{code}
data Tm {I : Set} (d : Desc I) : Size → I ─Scoped where
  `var : {s : Size} {i : I} →  [ Var i                     ⟶ Tm d (↑ s) i ]
  `con : {s : Size} {i : I} →  [ ⟦ d ⟧ (Scope (Tm d s)) i  ⟶ Tm d (↑ s) i ]
\end{code}
%</mu>

\begin{code}
-- Closed terms

TM : {I : Set} → Desc I → I → Set
TM d i = Tm d ∞ i []

-- Descriptions are closed under sums

module _ {I : Set} where

 infixr 5 _`+_
\end{code}
%<*sumcomb>
\begin{code}
 _`+_ : Desc I → Desc I → Desc I
 d `+ e =  `σ Bool $ λ isLeft →
           if isLeft then d else e
\end{code}
%</sumcomb>
\begin{code}
module _ {I : Set} {d e : Desc I} {X : List I → I ─Scoped}
         {A : Set} {i : I} {Γ : List I} where
\end{code}
%<*case>
\begin{code}
 case :  (⟦ d       ⟧ X i Γ → A) →
         (⟦ e       ⟧ X i Γ → A) →
         (⟦ d `+ e  ⟧ X i Γ → A)
\end{code}
%</case>
\begin{code}
 case l r (true   , t) = l t
 case l r (false  , t) = r t

module _ {I : Set} where
-- Descriptions are closed under products of recursive positions
\end{code}
%<*paircomb>
\begin{code}
 `Xs : List I → I → I → Desc I
 `Xs js j i = foldr (`X []) (`X js j (`∎ i)) js
\end{code}
%</paircomb>
\begin{code}
module _ {I : Set} {X : List I → I ─Scoped} {i j k : I} {Γ : List I} where
\end{code}
%<*pairunpair>
\begin{code}
 unXs :  (Δ : List I) → ⟦ `Xs Δ j i ⟧ X k Γ →
         All (λ i → X [] i Γ) Δ × X Δ j Γ × k ≡ i
\end{code}
%</pairunpair>
\begin{code}
 unXs = go id where

  go : (f : List I → List I) → (Δ : List I) →
       ⟦ foldr (`X []) (`X (f Δ) j (`∎ i)) Δ ⟧ X k Γ → All (λ i → X [] i Γ) Δ × X (f Δ) j Γ × k ≡ i
  go f []       (v , eq) = [] , v , eq
  go f (σ ∷ Δ)  (t , v)  = P.map (t ∷_) id $ go (f ∘ (σ ∷_)) Δ v
\end{code}


\begin{code}
-- Descriptions give rise to traversable functors

module _ {I : Set} {X Y : List I → I ─Scoped} where

 fmap : (d : Desc I) {Γ Δ : List I} {i : I} → (∀ Θ i → X Θ i Γ → Y Θ i Δ) → ⟦ d ⟧ X i Γ → ⟦ d ⟧ Y i Δ
 fmap (`σ A d)   f = P.map id (fmap (d _) f)
 fmap (`X Δ j d) f = P.map (f Δ j) (fmap d f)
 fmap (`∎ i)     f = id


module _ {I : Set} {X : List I → I ─Scoped} where
 fmap-id : (d : Desc I) {Γ : List I} {i : I} (v : ⟦ d ⟧ X i Γ) → fmap d (λ _ _ x → x) v ≡ v
 fmap-id (`σ A d)    (a , v)  = cong (a ,_) (fmap-id (d a) v)
 fmap-id (`X Δ j d)  (r , v)  = cong (r ,_) (fmap-id d v)
 fmap-id (`∎ x)      v        = refl

module _ {I : Set} {X Y Z : List I → I ─Scoped} where

 fmap² : (d : Desc I) {Γ Δ Θ : List I} {i : I}
         (f : ∀ Φ i → X Φ i Γ → Y Φ i Δ) (g : ∀ Φ i → Y Φ i Δ → Z Φ i Θ)
         (t : ⟦ d ⟧ X i Γ) → fmap  {I} {Y} {Z} d g (fmap d f t) ≡ fmap d (λ Φ i → g Φ i ∘ f Φ i) t
 fmap² (`σ A d)    f g (a , t)  = cong (_ ,_) (fmap² (d a) f g t)
 fmap² (`X Δ j d)  f g (r , t)  = cong (_ ,_) (fmap² d f g t)
 fmap² (`∎ i)      f g t        = refl


open import Category.Applicative

module _ {I : Set} {X : List I → I ─Scoped} {A : Set → Set} (app : RawApplicative A) where

 module A = RawApplicative app
 open A

 traverse : {i : I} (d : Desc I) → [ ⟦ d ⟧ (λ Δ j Γ → A (X Δ j Γ)) i ⟶ A ∘ ⟦ d ⟧ X i ]
 traverse (`σ A d)    (a , t)  = (λ b → a , b) A.<$> traverse (d a) t
 traverse (`X Δ j d)  (r , t)  = _,_ A.<$> r ⊛ traverse d t
 traverse (`∎ i)      t        = pure t
\end{code}

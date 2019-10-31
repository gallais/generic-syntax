\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Syntax where

open import Size
open import Data.Bool
open import Data.List.Base as L hiding ([_])
open import Data.List.Relation.Unary.All hiding (mapA; sequenceA)
open import Data.Product as Prod
open import Function hiding (case_of_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Var hiding (z; s)
open import Relation.Unary
open import Data.Environment as E hiding (sequenceA; uncurry)

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
\begin{code}
reindex : {I J : Set} → (I → J) → Desc I → Desc J
reindex f (`σ A d)   = `σ A λ a → reindex f (d a)
reindex f (`X Δ j d) = `X (L.map f Δ) (f j) (reindex f d)
reindex f (`∎ i)     = `∎ (f i)

private
  variable
    I : Set
    i σ : I
    Γ₁ Γ₂ : List I
    s : Size
    X Y : List I → I ─Scoped
\end{code}
%<*interp>
\begin{code}
⟦_⟧ : Desc I → (List I → I ─Scoped) → I ─Scoped
⟦ `σ A d    ⟧ X i Γ = Σ[ a ∈ A ] (⟦ d a ⟧ X i Γ)
⟦ `X Δ j d  ⟧ X i Γ = X Δ j Γ × ⟦ d ⟧ X i Γ
⟦ `∎ j      ⟧ X i Γ = i ≡ j
\end{code}
%</interp>
\begin{code}
-- Syntaxes: Free Relative Monad of a Description's Interpretation

\end{code}
%<*scope>
\begin{code}
Scope : I ─Scoped → List I → I ─Scoped
Scope T Δ i = (Δ ++_) ⊢ T i
\end{code}
%</scope>
\begin{code}
module _ {I : Set} where
\end{code}
%<*mu>
\begin{code}
 data Tm (d : Desc I) : Size → I ─Scoped where
   `var  : ∀[ Var i                     ⇒ Tm d (↑ s) i ]
   `con  : ∀[ ⟦ d ⟧ (Scope (Tm d s)) i  ⇒ Tm d (↑ s) i ]
\end{code}
%</mu>
\begin{code}

module _ {I i Γ} {d : Desc I} where

  `var-inj : ∀ {t u} → (Tm d ∞ i Γ ∋ `var t) ≡ `var u → t ≡ u
  `var-inj refl = refl

  `con-inj : ∀ {t u} → (Tm d ∞ i Γ ∋ `con t) ≡ `con u → t ≡ u
  `con-inj refl = refl

-- Closed terms
module _ {I : Set} where
\end{code}
%<*closed>
\begin{code}
  TM : Desc I → I → Set
  TM d i = Tm d ∞ i []
\end{code}
%</closed>
\begin{code}

-- Descriptions are closed under sums

module _ {I : Set} where

 infixr 5 _`+_

\end{code}
%<*descsum>
\begin{code}
 _`+_ : Desc I → Desc I → Desc I
 d `+ e = `σ Bool $ λ isLeft →
          if isLeft then d else e
\end{code}
%</descsum>
\begin{code}
module _ {I : Set} {d e : Desc I} {X : List I → I ─Scoped}
         {A : Set} {i : I} {Γ : List I} where
\end{code}
%<*case>
\begin{code}
 case : (⟦ d ⟧ X i Γ → A) → (⟦ e ⟧ X i Γ → A) →
        (⟦ d `+ e  ⟧ X i Γ → A)
 case l r (true   , t) = l t
 case l r (false  , t) = r t
\end{code}
%</case>
\begin{code}

module PAPERXS {I : Set} where
-- Descriptions are closed under products of recursive positions

\end{code}
%<*xs>
\begin{code}
 `Xs : List (List I × I) → Desc I → Desc I
 `Xs Δjs d = foldr (uncurry `X) d Δjs
\end{code}
%</xs>
\begin{code}

module PAPER {I : Set} {d : Desc I} {X : List I → I ─Scoped} {i : I} {Γ : List I} where
 open PAPERXS
\end{code}
%<*unxs>
\begin{code}
 unXs :  ∀ Δjs → ⟦ `Xs Δjs d ⟧ X i Γ →
         All (uncurry $ λ Δ j → X Δ j Γ) Δjs × ⟦ d ⟧ X i Γ

 unXs []       v        = [] , v
 unXs (σ ∷ Δ)  (r , v)  = Prod.map₁ (r ∷_) (unXs Δ v)
\end{code}
%</unxs>
\begin{code}

module _ {I : Set} where
-- Descriptions are closed under products of recursive positions

\end{code}
%<*xs>
\begin{code}
 `Xs : List I → Desc I → Desc I
 `Xs js d = foldr (`X []) d js
\end{code}
%</xs>
\begin{code}

module _ {I : Set} {d : Desc I} {X : List I → I ─Scoped} {i : I} {Γ : List I} where

 unXs : ∀ Δ → ⟦ `Xs Δ d ⟧ X i Γ → (Δ ─Env) (X []) Γ × ⟦ d ⟧ X i Γ
 unXs []       v       = ε , v
 unXs (σ ∷ Δ)  (r , v) = Prod.map₁ (_∙ r) (unXs Δ v)

-- Descriptions give rise to traversable functors

module _ {I : Set} {X Y : List I → I ─Scoped} {Γ Δ} {i} where

\end{code}
%<*fmap>
\begin{code}
 fmap :  (d : Desc I) → (∀ Θ i → X Θ i Γ → Y Θ i Δ) → ⟦ d ⟧ X i Γ → ⟦ d ⟧ Y i Δ
 fmap (`σ A d)    f = Prod.map₂ (fmap (d _) f)
 fmap (`X Δ j d)  f = Prod.map (f Δ j) (fmap d f)
 fmap (`∎ i)      f = id
\end{code}
%</fmap>
\begin{code}

 fmap-ext : (d : Desc I) {f g : ∀ Θ i → X Θ i Γ → Y Θ i Δ} →
            (f≈g : ∀ Θ i x → f Θ i x ≡ g Θ i x) (v : ⟦ d ⟧ X i Γ) →
            fmap d f v ≡ fmap d g v
 fmap-ext (`σ A d)   f≈g (a , v) = cong (a ,_) (fmap-ext (d a) f≈g v)
 fmap-ext (`X Δ j d) f≈g (r , v) = cong₂ _,_ (f≈g Δ j r) (fmap-ext d f≈g v)
 fmap-ext (`∎ i)     f≈g v       = refl

module _ {I : Set} {X : List I → I ─Scoped} where

 fmap-id : (d : Desc I) {Γ : List I} {i : I} (v : ⟦ d ⟧ X i Γ) → fmap d (λ _ _ x → x) v ≡ v
 fmap-id (`σ A d)    (a , v)  = cong (a ,_) (fmap-id (d a) v)
 fmap-id (`X Δ j d)  (r , v)  = cong (r ,_) (fmap-id d v)
 fmap-id (`∎ x)      v        = refl

module _ {I : Set} {X Y Z : List I → I ─Scoped} where

 fmap² : (d : Desc I) {Γ Δ Θ : List I} {i : I}
         (f : ∀ Φ i → X Φ i Γ → Y Φ i Δ) (g : ∀ Φ i → Y Φ i Δ → Z Φ i Θ)
         (t : ⟦ d ⟧ X i Γ) →
         fmap  {I} {Y} {Z} d g (fmap d f t) ≡ fmap d (λ Φ i → g Φ i ∘ f Φ i) t
 fmap² (`σ A d)    f g (a , t)  = cong (_ ,_) (fmap² (d a) f g t)
 fmap² (`X Δ j d)  f g (r , t)  = cong (_ ,_) (fmap² d f g t)
 fmap² (`∎ i)      f g t        = refl


open import Category.Applicative

module _ {A : Set → Set} {{app : RawApplicative A}} where

 module A = RawApplicative app
 open A

 sequenceA : (d : Desc I) →
             ∀[ ⟦ d ⟧ (λ Δ j Γ → A (X Δ j Γ)) i ⇒ A ∘ ⟦ d ⟧ X i ]
 sequenceA (`σ A d)    (a , t)  = (λ b → a , b) A.<$> sequenceA (d a) t
 sequenceA (`X Δ j d)  (r , t)  = _,_ A.<$> r ⊛ sequenceA d t
 sequenceA (`∎ i)      t        = pure t

 mapA : (d : Desc I) →
        (f : ∀ Δ j → X Δ j Γ₁ → A (Y Δ j Γ₂))
        → ⟦ d ⟧ X σ Γ₁ → A (⟦ d ⟧ Y σ Γ₂)
 mapA d f = sequenceA d ∘ fmap d f

-- Desc Morphisms

record DescMorphism {I : Set} (d e : Desc I) : Set₁ where
  constructor MkDescMorphism
  field apply : ∀ {X i Δ} → ⟦ d ⟧ X i Δ → ⟦ e ⟧ X i Δ

module _ {I : Set} {d e : Desc I} where

  map^Tm : DescMorphism d e → ∀ {i σ Γ} → Tm d i σ Γ → Tm e i σ Γ
  map^Tm f (`var v) = `var v
  map^Tm f (`con t) = `con (DescMorphism.apply f (fmap d (λ _ _ → map^Tm f) t))
\end{code}

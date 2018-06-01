module Generic.Syntax where

open import Size
open import Data.Bool
open import Data.List.Base as L hiding ([_])
open import Data.Product as P hiding (,_)
open import Function hiding (case_of_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import var
open import indexed
open import environment as E hiding (traverse)

-- Descriptions and their Interpretation

data Desc (I : Set) : Set₁ where
  `σ : (A : Set) → (A → Desc I)  → Desc I
  `X : List I → I → Desc I       → Desc I
  `∎ : I                         → Desc I

reindex : {I J : Set} → (I → J) → Desc I → Desc J
reindex f (`σ A d)   = `σ A λ a → reindex f (d a)
reindex f (`X Δ j d) = `X (L.map f Δ) (f j) (reindex f d)
reindex f (`∎ i)     = `∎ (f i)

⟦_⟧ : {I : Set} → Desc I → (List I → I ─Scoped) → I ─Scoped
⟦ `σ A d    ⟧ X i Γ = Σ[ a ∈ A ] (⟦ d a ⟧ X i Γ)
⟦ `X Δ j d  ⟧ X i Γ = X Δ j Γ × ⟦ d ⟧ X i Γ
⟦ `∎ i′     ⟧ X i Γ = i ≡ i′

-- Syntaxes: Free Relative Monad of a Description's Interpretation

Scope : {I : Set} → I ─Scoped → List I → I ─Scoped
Scope T Δ i = (Δ ++_) ⊢ T i

data Tm {I : Set} (d : Desc I) : Size → I ─Scoped where
  `var : {s : Size} {i : I} →  [ Var i                     ⟶ Tm d (↑ s) i ]
  `con : {s : Size} {i : I} →  [ ⟦ d ⟧ (Scope (Tm d s)) i  ⟶ Tm d (↑ s) i ]

`con-inj : ∀ {I i Γ} {d : Desc I} {t u : ⟦ d ⟧ (Scope (Tm d ∞)) i Γ} →
           (Tm d ∞ i Γ ∋ `con t) ≡ `con u → t ≡ u
`con-inj refl = refl

-- Closed terms

TM : {I : Set} → Desc I → I → Set
TM d i = Tm d ∞ i []

-- Descriptions are closed under sums

module _ {I : Set} where

 infixr 5 _`+_

 _`+_ : Desc I → Desc I → Desc I
 d `+ e =  `σ Bool $ λ isLeft →
           if isLeft then d else e

module _ {I : Set} {d e : Desc I} {X : List I → I ─Scoped}
         {A : Set} {i : I} {Γ : List I} where

 case :  (⟦ d       ⟧ X i Γ → A) →
         (⟦ e       ⟧ X i Γ → A) →
         (⟦ d `+ e  ⟧ X i Γ → A)

 case l r (true   , t) = l t
 case l r (false  , t) = r t

module _ {I : Set} where
-- Descriptions are closed under products of recursive positions

 `Xs : List I → Desc I → Desc I
 `Xs js d = foldr (`X []) d js

module _ {I : Set} {d : Desc I} {X : List I → I ─Scoped} {i : I} {Γ : List I} where

 unXs :  (Δ : List I) → ⟦ `Xs Δ d ⟧ X i Γ →
         (Δ ─Env) (X []) Γ × ⟦ d ⟧ X i Γ

 unXs []       v       = ε , v
 unXs (σ ∷ Δ)  (r , v) = P.map (_∙ r) id (unXs Δ v)

-- Descriptions give rise to traversable functors

module _ {I : Set} {X Y : List I → I ─Scoped} where

 fmap : (d : Desc I) {Γ Δ : List I} {i : I} →
        (∀ Θ i → X Θ i Γ → Y Θ i Δ) → ⟦ d ⟧ X i Γ → ⟦ d ⟧ Y i Δ
 fmap (`σ A d)   f = P.map id (fmap (d _) f)
 fmap (`X Δ j d) f = P.map (f Δ j) (fmap d f)
 fmap (`∎ i)     f = id

 fmap-ext : (d : Desc I) {Γ Δ : List I} {i : I} {f g : ∀ Θ i → X Θ i Γ → Y Θ i Δ} →
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

module _ {I : Set} {X : List I → I ─Scoped} {A : Set → Set} (app : RawApplicative A) where

 module A = RawApplicative app
 open A

 traverse : {i : I} (d : Desc I) → [ ⟦ d ⟧ (λ Δ j Γ → A (X Δ j Γ)) i ⟶ A ∘ ⟦ d ⟧ X i ]
 traverse (`σ A d)    (a , t)  = (λ b → a , b) A.<$> traverse (d a) t
 traverse (`X Δ j d)  (r , t)  = _,_ A.<$> r ⊛ traverse d t
 traverse (`∎ i)      t        = pure t

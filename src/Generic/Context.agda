module Generic.Context where

open import Size
open import Data.Bool
open import Data.List.Base as L hiding ([_])
open import Data.Product as Prod
open import Function hiding (case_of_)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Var
open import Data.Environment as E

open import Generic.Syntax
open import Data.Empty
open import Data.Sum renaming (inj₁ to here; inj₂ to right)

⟦_⟧' : {I : Set} → Desc I → (C M J : List I → I ─Scoped) → I ─Scoped
⟦ `σ A d    ⟧' C M J i Γ = Σ[ a ∈ A ] (⟦ d a ⟧' C M J i Γ)
⟦ `X Δ j d  ⟧' C M J i Γ = (M Δ j Γ × ⟦ d ⟧ J i Γ)
                         ⊎ (C Δ j Γ × ⟦ d ⟧' C M J i Γ)
⟦ `∎ i′     ⟧' C M J i Γ = ⊥

Eq : ∀ {I} → (List I × I × List I) → List I → I ─Scoped
Eq ΔjΓ Δ' j' Γ' = ΔjΓ ≡ (Δ' , j' , Γ')

record ∇∙ {I} (d : Desc I) (i : I) (Γ : List I) (X : List I → I ─Scoped) : Set where
  constructor _,_
  field {Δ}  : List I
        {j}  : I
        {Γ'} : List I
        ctx  : ⟦ d ⟧' X (Eq (Δ , j , Γ')) X i Γ
        me   : X Δ j Γ'

plug : ∀ {I} (d : Desc I) {X i Γ} → ∇∙ d i Γ X → ⟦ d ⟧ X i Γ
plug (`σ A d)   ((a , c)             , x) = a , plug (d a) (c , x)
plug (`X Δ j d) ((here (refl , ⟦d⟧)) , x) = x , ⟦d⟧
plug (`X Δ j d) ((right (x' , c))     , x) = x' , plug d (c , x)
plug (`∎ i)     (()                  , x)

Focus : ∀ {I} (d : Desc I) → I → List I →
        (List I → I ─Scoped) → (List I → I ─Scoped)
Focus d i Γ X Δ j Γ' = Σ[ c ∈ ∇∙ d i Γ X ] Eq (Δ , j , Γ')(c .∇∙.Δ) (c .∇∙.j) (c .∇∙.Γ')

module _ {I : Set} {X} {i : I} {Γ} where

  tack : ∀ {A d} (a : A) → ∇∙ (d a) i Γ X → ∇∙ (`σ A d) i Γ X
  tack a (ctx , me) = ((a , ctx) , me)

  bore : ∀ {Δ j d} x → ∇∙ d i Γ X → ∇∙ (`X Δ j d) i Γ X
  bore x (ctx , me) = right (x , ctx) , me

  visit : ∀ (d : Desc I) → ⟦ d ⟧ X i Γ → ⟦ d ⟧ (Focus d i Γ X) i Γ
  visit (`σ A d)   (a , c) = a
    , fmap (d a) (λ where _ _ (c , eq) → tack a c , eq) (visit (d a) c)
  visit (`X Δ j d) (x , c) = ((here (refl , c) , x) , refl)
    , fmap d (λ where _ _ (c , eq) → bore x c , eq) (visit d c)
  visit (`∎ i)     c       = c

module _ {I X} {i : I} {Γ} where

  Ftack : ∀ {A d} (a : A) → ∀ {Δ j Γ'} →
          Focus (d a) i Γ X Δ j Γ' → Focus (`σ A d) i Γ X Δ j Γ'
  Ftack a (c , e) = tack a c , e

  Fbore : ∀ {Δ j d} x → ∀ {Δ' j' Γ'} →
          Focus d i Γ X Δ' j' Γ' → Focus (`X Δ j d) i Γ X Δ' j' Γ'
  Fbore x (c , e) = bore x c , e

module _ {I : Set} {X Y : List I → I ─Scoped} where

  cobind : ∀ d {i Γ} → (∀ {Δ j Γ'} → Focus d i Γ X Δ j Γ' → Y Δ j Γ')
                     → (∀ {Δ j Γ'} → Focus d i Γ X Δ j Γ' → Focus d i Γ Y Δ j Γ')
  cobind (`σ A d)   f (((a , c)         , m) , e) =
    Ftack a (cobind (d a) (f ∘ Ftack a) ((c , m) , e))
  cobind (`X Δ j d) f pos@((here (refl , c) , m) , refl) =
    (here (refl , fmap d (λ _ _ → f ∘ Fbore m) (visit d c))
    , f pos)
    , refl
  cobind (`X Δ j d) f ((right (x , c) , m) , e) =
    let y = f ((here (refl , plug d (c , m)) , x) , refl) in
    Fbore y (cobind d (f ∘ Fbore x) ((c , m) , e))
  cobind (`∎ i)     f ()


{-
  relator : ∀ {d} (d' : Desc B I)
            (pt pu : ⟦ d' ⟧ (Scope (Tm d)) → Tm d) →
            Desc B (Tuple d)
-}

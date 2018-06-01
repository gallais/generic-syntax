module Generic.Semantics.Elaboration.State.Type where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function

open import var
open import Generic.Syntax.STLC+State
open import Generic.Syntax.STLC+Product

-- Translating from State-types to Product-types
M⟦_⟧ : MType → PType
M⟦ α     ⟧ = α
M⟦ 𝟙     ⟧ = 𝟙
M⟦ σ ⇒ τ ⟧ = M⟦ σ ⟧ ⇒ M⟦ τ ⟧
M⟦ M σ   ⟧ = α ⇒ (α ⊗ M⟦ σ ⟧)

-- The translation is injective
⇒-inj : {σ τ σ₁ τ₁ : PType} → (PType ∋ σ ⇒ τ) ≡ σ₁ ⇒ τ₁ → σ ≡ σ₁ × τ ≡ τ₁
⇒-inj refl = refl , refl

⊗-inj : {σ τ σ₁ τ₁ : PType} → (PType ∋ σ ⊗ τ) ≡ σ₁ ⊗ τ₁ → σ ≡ σ₁ × τ ≡ τ₁
⊗-inj refl = refl , refl

M⟦⟧-inj : Injective M⟦_⟧
M⟦⟧-inj = record { inj = go _ _ } where
  go : (σ τ : MType) → M⟦ σ ⟧ ≡ M⟦ τ ⟧ → σ ≡ τ
  go α α eq = refl
  go α 𝟙 ()
  go α (τ ⇒ τ₁) ()
  go α (M τ) ()
  go 𝟙 α ()
  go 𝟙 𝟙 eq = refl
  go 𝟙 (τ ⇒ τ₁) ()
  go 𝟙 (M τ) ()
  go (σ ⇒ σ₁) α ()
  go (σ ⇒ σ₁) 𝟙 ()
  go (σ ⇒ σ₁) (τ ⇒ τ₁) eq =
    cong₂ _⇒_ (go σ τ (proj₁ (⇒-inj eq))) (go σ₁ τ₁ (proj₂ (⇒-inj eq)))
  go (σ ⇒ α) (M τ) ()
  go (σ ⇒ 𝟙) (M τ) ()
  go (σ ⇒ (σ₁ ⇒ σ₂)) (M τ) ()
  go (σ ⇒ M σ₁) (M τ) ()
  go (M σ) α ()
  go (M σ) 𝟙 ()
  go (M σ) (τ ⇒ α) ()
  go (M σ) (τ ⇒ 𝟙) ()
  go (M σ) (τ ⇒ (τ₁ ⇒ τ₂)) ()
  go (M σ) (τ ⇒ M τ₁) ()
  go (M σ) (M τ) eq = cong M (go σ τ (proj₂ (⊗-inj (proj₂ (⇒-inj eq)))))


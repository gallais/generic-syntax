\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Semantics.Elaboration.State where

open import Data.Product
open import Data.List.Base as L hiding (lookup)
open import Relation.Binary.PropositionalEquality
open import Function.Base

open import Data.Var as V
open import Data.Var.Varlike
open import Data.Environment as E
open import Generic.Syntax
open import Generic.Syntax.STLC+State
open import Generic.Syntax.STLC+Product
open import Generic.Semantics
open import Generic.Semantics.Syntactic

-- Importing the proven-injective type translation

M⟦_⟧ : MType → PType
M⟦ α     ⟧ = α
M⟦ 𝟙     ⟧ = 𝟙
M⟦ σ `→ τ ⟧ = M⟦ σ ⟧ `→ M⟦ τ ⟧
M⟦ M σ   ⟧ = α `→ (α ⊗ M⟦ σ ⟧)

`→-inj : {σ τ σ₁ τ₁ : PType} → (PType ∋ σ `→ τ) ≡ σ₁ `→ τ₁ → σ ≡ σ₁ × τ ≡ τ₁
`→-inj refl = refl , refl

⊗-inj : {σ τ σ₁ τ₁ : PType} → (PType ∋ σ ⊗ τ) ≡ σ₁ ⊗ τ₁ → σ ≡ σ₁ × τ ≡ τ₁
⊗-inj refl = refl , refl

M⟦⟧-inj : Injective M⟦_⟧
M⟦⟧-inj = record { inj = go _ _ } where
  go : (σ τ : MType) → M⟦ σ ⟧ ≡ M⟦ τ ⟧ → σ ≡ τ
  go α α eq = refl
  go α 𝟙 ()
  go α (τ `→ τ₁) ()
  go α (M τ) ()
  go 𝟙 α ()
  go 𝟙 𝟙 eq = refl
  go 𝟙 (τ `→ τ₁) ()
  go 𝟙 (M τ) ()
  go (σ `→ σ₁) α ()
  go (σ `→ σ₁) 𝟙 ()
  go (σ `→ σ₁) (τ `→ τ₁) eq =
    cong₂ _`→_ (go σ τ (proj₁ (`→-inj eq))) (go σ₁ τ₁ (proj₂ (`→-inj eq)))
  go (σ `→ α) (M τ) ()
  go (σ `→ 𝟙) (M τ) ()
  go (σ `→ (σ₁ `→ σ₂)) (M τ) ()
  go (σ `→ M σ₁) (M τ) ()
  go (M σ) α ()
  go (M σ) 𝟙 ()
  go (M σ) (τ `→ α) ()
  go (M σ) (τ `→ 𝟙) ()
  go (M σ) (τ `→ (τ₁ `→ τ₂)) ()
  go (M σ) (τ `→ M τ₁) ()
  go (M σ) (M τ) eq = cong M (go σ τ (proj₂ (⊗-inj (proj₂ (`→-inj eq)))))

-- Environment of the elaboration semantics:
-- Variables of the translated type
MVAR : MType ─Scoped
MVAR σ Γ = Var M⟦ σ ⟧ (L.map M⟦_⟧ Γ)

-- Because M⟦_⟧ is injective, MVAR is VarLike
vl^MVAR : VarLike MVAR
new   vl^MVAR         = z
th^𝓥 vl^MVAR {σ} v ρ = M⟦_⟧ V.<$> (lookup ρ {σ} (M⟦⟧-inj <$>⁻¹ v))

-- Target of the Elaboration process
MTM : MType ─Scoped
MTM σ Γ = Tm STLCPr _ M⟦ σ ⟧ (L.map M⟦_⟧ Γ)

-- Traditional Elaboration Semantics from State to Product
UnState : Semantics STLCSt MVAR MTM
Semantics.th^𝓥 UnState {σ} = th^𝓥 vl^MVAR {σ}
Semantics.var   UnState = `var
Semantics.alg   UnState = let open Generic.Syntax.STLC+Product.PATTERNS in λ where
  (App σ τ , f , t , refl) → APP f t
  (Lam σ τ , b , refl)     → LAM (reify {𝓒 = MTM} vl^MVAR (σ ∷ []) τ b)
  (One     , refl)         → ONE
  (Get     , refl)         → LAM (PRD (`var z) (`var z))
  (Put     , t , refl)     → LAM (PRD (`var z) ONE)
  (Ret σ   , t , refl)     → LAM (PRD (`var z) (ren weaken t))
  (Bnd σ τ , m , f , refl) → let f′ = ren weaken f ; m′ = ren weaken m in
                             LAM (APP (CUR f′) (SWP (APP m′ (`var z))))
\end{code}

module Generic.Semantics.Elaboration.State where

open import Data.Product
open import Data.List.Base as L hiding (lookup)
open import Relation.Binary.PropositionalEquality
open import Function

open import var as V
open import varlike
open import environment as E
open import Generic.Syntax
open import Generic.Syntax.STLC+State
open import Generic.Syntax.STLC+Product
open import Generic.Semantics
open import Generic.Semantics.Syntactic

-- Importing the proven-injective type translation
open import Generic.Semantics.Elaboration.State.Type

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
UnState : Sem STLCSt MVAR MTM
Sem.th^𝓥 UnState {σ} = th^𝓥 vl^MVAR {σ}
Sem.var   UnState = `var
Sem.alg   UnState = let open Generic.Syntax.STLC+Product.PATTERNS in λ where
  (App σ τ , f , t , refl) → APP f t
  (Lam σ τ , b , refl)     → LAM (reify {𝓒 = MTM} vl^MVAR (σ ∷ []) τ b)
  (One     , refl)         → ONE
  (Get     , refl)         → LAM (PRD (`var z) (`var z))
  (Put     , t , refl)     → LAM (PRD (`var z) ONE)
  (Ret σ   , t , refl)     → LAM (PRD (`var z) (ren extend t))
  (Bnd σ τ , m , f , refl) → let f′ = ren extend f ; m′ = ren extend m in
                             LAM (APP (CUR f′) (SWP (APP m′ (`var z))))

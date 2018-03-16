module Generic.AltSyntax where

open import Level
open import Size
open import Data.Bool
open import Data.List.All
open import Data.List.All.Properties
open import Data.List.Base as L hiding ([_])
open import Data.Product as P hiding (,_)
open import Function hiding (case_of_)
open import Function.Equality
open import Function.Inverse
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open import var hiding (_<$>_)
open import varlike
open import indexed
open import environment as E hiding (traverse ; _<$>_)
open import Generic.Syntax
open import Generic.Semantics

LAMBS : {I : Set} → (I → Set) → (I → Set) → List I → I ─Scoped
LAMBS V T [] j Γ = T j
LAMBS V T Δ  j Γ = (Δ ─Env) (κ ∘′ V) [] → T j

data PHOAS {I : Set} (d : Desc I) (V : I → Set) : Size → I → Set where
  V[_] : ∀ {s σ} → V σ → PHOAS d V (↑ s) σ
  T[_] : ∀ {s σ} → ⟦ d ⟧ (LAMBS V (PHOAS d V s)) σ [] → PHOAS d V (↑ s) σ

module ToPHOAS {I : Set} {V : I → Set} where

  toPHOAS : ∀ d → Sem d (κ ∘′ V) (κ ∘′ PHOAS d V ∞)
  Sem.th^𝓥  (toPHOAS d) = λ v _ → v
  Sem.var    (toPHOAS d) = V[_]
  Sem.alg    (toPHOAS d) = T[_] ∘′ fmap d (λ Δ → binders Δ) where

    binders : ∀ {Γ} Δ i → Kripke (κ ∘′ V) (κ ∘′ PHOAS d V ∞) Δ i Γ → LAMBS V (PHOAS d V ∞) Δ i []
    binders []        i kr = kr
    binders Δ@(_ ∷ _) i kr = λ vs → kr (base vl^Var) ((λ v → v) E.<$> vs)

open import Data.String as String

Names : {I : Set} → (I → Set) → List I → I ─Scoped
Names T Δ j Γ = All (κ String) Δ × T j

data Raw {I : Set} (d : Desc I) : Size → I → Set where
  V[_] : ∀ {s σ} → String → Raw d (↑ s) σ
  T[_] : ∀ {s σ} → ⟦ d ⟧ (Names (Raw d s)) σ [] → Raw d (↑ s) σ

open import Data.Maybe hiding (All)
open import Category.Monad

module ScopeCheck {I : Set} {d : Desc I} (I-dec : (i j : I) → Dec (i ≡ j)) where

 open RawMonad (monad {zero})

 varCheck : String → ∀ σ Γ → All (κ String) Γ → Maybe (Var σ Γ)
 varCheck str σ []       []         = nothing
 varCheck str σ (τ ∷ Γ)  (nm ∷ scp) with nm String.≟ str
 ... | no ¬p = s <$> varCheck str σ Γ scp
 ... | yes p with I-dec σ τ
 ... | no ¬eq = nothing
 ... | yes eq = just (subst (Var _ ∘′ (_∷ Γ)) eq z)


 scopeCheck     : ∀ {s} σ Γ → All (κ String) Γ → Raw d s σ → Maybe (Tm d s σ Γ)
 scopeCheckBody : ∀ Γ → All (κ String) Γ → ∀ {s} Δ σ → Names (Raw d s) Δ σ Γ → Maybe (Scope (Tm d s) Δ σ Γ)

 scopeCheck σ Γ scp V[ v ] = `var <$> varCheck v σ Γ scp
 scopeCheck σ Γ scp T[ t ] = `con <$> traverse rawIApplicative d
                                      (fmap d (scopeCheckBody Γ scp) t)

 scopeCheckBody Γ scp Δ σ (nms , b) =
   scopeCheck σ (Δ L.++ Γ) (Inverse.to ++↔ ⟨$⟩ (nms , scp)) b


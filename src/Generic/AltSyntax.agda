{-# OPTIONS --safe --sized-types #-}

module Generic.AltSyntax where

open import Level
open import Size
open import Category.Monad

open import Data.Bool
open import Data.List.Relation.Unary.All hiding (sequenceA)
open import Data.List.Relation.Unary.All.Properties
open import Data.List.Base as L hiding ([_])
open import Data.Maybe.Base
open import Data.Sum.Base
import Data.Sum.Categorical.Left as SC
open import Data.Product
open import Data.String as String

open import Function hiding (case_of_)
import Function.Equality as FEq
import Function.Inverse as FInv
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Function

open import Data.Var hiding (_<$>_)
open import Data.Var.Varlike
open import Data.Environment as E hiding (sequenceA ; _<$>_)
open import Generic.Syntax
open import Generic.Semantics

LAMBS : {I : Set} → (I → Set) → (I → Set) → List I → I ─Scoped
LAMBS V T [] j Γ = T j
LAMBS V T Δ  j Γ = (Δ ─Env) (const ∘′ V) [] → T j

data PHOAS {I : Set} (d : Desc I) (V : I → Set) : Size → I → Set where
  V[_] : ∀ {s σ} → V σ → PHOAS d V (↑ s) σ
  T[_] : ∀ {s σ} → ⟦ d ⟧ (LAMBS V (PHOAS d V s)) σ [] → PHOAS d V (↑ s) σ

module ToPHOAS {I : Set} {V : I → Set} where

  toPHOAS : ∀ d → Semantics d (const ∘′ V) (const ∘′ PHOAS d V ∞)
  Semantics.th^𝓥  (toPHOAS d) = λ v _ → v
  Semantics.var    (toPHOAS d) = V[_]
  Semantics.alg    (toPHOAS d) = T[_] ∘′ fmap d (λ Δ → binders Δ) where

    binders : ∀ {Γ} Δ i → Kripke (const ∘′ V) (const ∘′ PHOAS d V ∞) Δ i Γ → LAMBS V (PHOAS d V ∞) Δ i []
    binders []        i kr = kr
    binders Δ@(_ ∷ _) i kr = λ vs → kr (base vl^Var) ((λ v → v) E.<$> vs)

Names : {I : Set} → (I → Set) → List I → I ─Scoped
Names T [] j Γ = T j
Names T Δ  j Γ = All (const String) Δ × T j

data Raw (A : Set) {I : Set} (d : Desc I) : Size → I → Set where
  `var : ∀ {s σ} → A → String → Raw A d (↑ s) σ
  `con : ∀ {s σ} → ⟦ d ⟧ (Names (Raw A d s)) σ [] → Raw A d (↑ s) σ

module ScopeCheck {E I : Set} {d : Desc I} (I-dec : (i j : I) → Dec (i ≡ j)) where

 private
   M : Set → Set
   M = (E × String) ⊎_
 open RawMonad (SC.monad (E × String) zero)

 instance _ =  rawIApplicative

 varCheck : E × String → ∀ σ Γ → All (const String) Γ → M (Var σ Γ)
 varCheck v           σ []       []         = inj₁ v
 varCheck v@(e , str) σ (τ ∷ Γ)  (nm ∷ scp) with nm String.≟ str
 ... | no ¬p = s <$> varCheck v σ Γ scp
 ... | yes p with I-dec σ τ
 ... | no ¬eq = inj₁ v
 ... | yes eq = inj₂ (subst (Var _ ∘′ (_∷ Γ)) eq z)

 scopeCheck    : ∀ {s} σ Γ → All (const String) Γ → Raw E d s σ → M (Tm d s σ Γ)

 scopeCheckBody : ∀ Γ → All (const String) Γ →
                  ∀ {s} Δ σ → Names (Raw E d s) Δ σ [] → M (Scope (Tm d s) Δ σ Γ)

 scopeCheck σ Γ scp (`var e v) = `var <$> varCheck (e , v) σ Γ scp
 scopeCheck σ Γ scp (`con b)   = `con <$> sequenceA d (fmap d (scopeCheckBody Γ scp) b)

 scopeCheckBody Γ scp []        σ b         = scopeCheck σ Γ scp b
 scopeCheckBody Γ scp Δ@(_ ∷ _) σ (nms , b) =
   scopeCheck σ (Δ L.++ Γ) (FInv.Inverse.to ++↔ FEq.⟨$⟩ (nms , scp)) b

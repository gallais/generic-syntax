\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.AltSyntax where

open import Level
open import Size
open import Data.Bool
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.All.Properties
open import Data.List.Base as List hiding ([_])
open import Data.Product as Prod
open import Function hiding (case_of_)
import Function.Equality as FEq
import Function.Inverse as FInv
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Relation.Unary
open import Relation.Nullary

open import Data.Var as Var using (Var; _─Scoped)
open import Data.Var.Varlike
open import Data.Environment as E hiding (_<$>_; sequenceA)
open import Generic.Syntax
open import Generic.Semantics

private
  variable
    I : Set
    σ : I
    s : Size
    V : I → Set
    Γ : List I

module PHOAS (d : Desc I) (V : I → Set) where

  PHOVar : I ─Scoped
  PHOVar i _ = V i

  LAMBS : (I → Set) → List I → I ─Scoped
  LAMBS T [] j Γ = T j
  LAMBS T Δ  j Γ = (Δ ─Env) PHOVar [] → T j

  data PHOAS : Size → I → Set where
    V[_] : V σ → PHOAS (↑ s) σ
    T[_] : ⟦ d ⟧ (LAMBS (PHOAS s)) σ [] → PHOAS (↑ s) σ

  PHOTm : Size → I ─Scoped
  PHOTm s i _ = PHOAS s i

  toPHOAS : Semantics d PHOVar (PHOTm ∞)
  Semantics.th^𝓥  toPHOAS = λ v _ → v
  Semantics.var   toPHOAS = V[_]
  Semantics.alg   toPHOAS = T[_] ∘′ fmap d binders where

    binders : ∀ Δ i → Kripke PHOVar (PHOTm ∞) Δ i Γ → LAMBS (PHOAS ∞) Δ i []
    binders []        i kr = kr
    binders Δ@(_ ∷ _) i kr = λ vs → kr (base vl^Var) (id E.<$> vs)

open import Data.String as String

Names : (I → Set) → List I → I ─Scoped
Names T Δ j Γ = All (const String) Δ × T j

data Raw {I : Set} (d : Desc I) : Size → I → Set where
  V[_] : ∀ {s σ} → String → Raw d (↑ s) σ
  T[_] : ∀ {s σ} → ⟦ d ⟧ (Names (Raw d s)) σ [] → Raw d (↑ s) σ

open import Data.Maybe.Base
open import Data.Maybe.Categorical using (monad)
open import Category.Monad

module SCOPE {I : Set} {d : Desc I} (I-dec : (i j : I) → Dec (i ≡ j)) where

 open RawMonad (monad {zero})
 instance _ = rawIApplicative

 varCheck : String → ∀ σ Γ → All (const String) Γ → Maybe (Var σ Γ)
 varCheck str σ []       []         = nothing
 varCheck str σ (τ ∷ Γ)  (nm ∷ scp) with nm String.≟ str
 ... | no ¬p = Var.s <$> varCheck str σ Γ scp
 ... | yes p with I-dec σ τ
 ... | no ¬eq = nothing
 ... | yes eq = just (subst (Var _ ∘′ (_∷ Γ)) eq Var.z)


 scopeCheck     : ∀ {s} σ Γ → All (const String) Γ → Raw d s σ → Maybe (Tm d s σ Γ)
 scopeCheckBody : ∀ Γ → All (const String) Γ → ∀ {s} Δ σ → Names (Raw d s) Δ σ Γ → Maybe (Scope (Tm d s) Δ σ Γ)

 scopeCheck σ Γ scp V[ v ] = `var <$> varCheck v σ Γ scp
 scopeCheck σ Γ scp T[ t ] = `con <$> sequenceA d (fmap d (scopeCheckBody Γ scp) t)

 scopeCheckBody Γ scp Δ σ (nms , b) =
   scopeCheck σ (Δ List.++ Γ) (FInv.Inverse.to ++↔ FEq.⟨$⟩ (nms , scp)) b
\end{code}

{-# OPTIONS --safe --sized-types #-}

open import Generic.Syntax

module Generic.Syntax.PHOAS {I : Set} (d : Desc I) (V : I → Set) where

open import Size
open import Data.List.Base as L hiding ([_])
open import Function

open import Data.Var hiding (_<$>_)
open import Data.Environment
open import Generic.Semantics

private
  variable
    Γ : List I

LAMBS : (I → Set) → List I → I ─Scoped
LAMBS T [] j Γ = T j
LAMBS T Δ  j Γ = (Δ ─Env) (const ∘′ V) (Δ ++ Γ) → T j

data PHOAS (d : Desc I) : Size → I → Set where
  V[_] : ∀ {s σ} → V σ → PHOAS d (↑ s) σ
  T[_] : ∀ {s σ} → ⟦ d ⟧ (LAMBS (PHOAS d s)) σ [] → PHOAS d (↑ s) σ

binders : ∀ Δ σ →
          Kripke (const ∘′ V) (const ∘′ PHOAS d ∞) Δ σ Γ →
          LAMBS (PHOAS d ∞) Δ σ []
binders []        i kr = kr
binders Δ@(_ ∷ _) i kr = λ vs → kr identity (id <$> vs)

toPHOAS : Semantics d (const ∘′ V) (const ∘′ PHOAS d ∞)
Semantics.th^𝓥  toPHOAS = λ v _ → v
Semantics.var    toPHOAS = V[_]
Semantics.alg    toPHOAS = T[_] ∘′ fmap d binders

\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Data.Pred where

open import Data.Var hiding (_<$>_)
open import Data.Environment
open import Agda.Builtin.List
open import Function
open import Relation.Unary using (IUniversal; _⇒_)

private
  variable
    I : Set
    σ : I
    Γ Δ Θ : List I
    T : I ─Scoped

record Pred (T : I ─Scoped) : Set₁ where
  constructor mkPred
  field pred : ∀ σ → ∀[ T σ ⇒ const Set ]
open Pred public

record All (𝓟 : Pred T) (Γ : List I) (ρ : (Γ ─Env) T Δ) : Set where
  constructor packᴾ
  field lookupᴾ : (k : Var σ Γ) → pred 𝓟 σ (lookup ρ k)
open All public

private
  variable
    𝓟 : Pred T

_<$>ᴾ_ : {f : {i : I} → T i Δ → T i Θ} →
         (∀ {i} {t : T i Δ} → pred 𝓟 i t → pred 𝓟 i (f t)) →
         {ρ : (Γ ─Env) T Δ} → All 𝓟 Γ ρ → All 𝓟 Γ (f <$> ρ)
lookupᴾ (F <$>ᴾ ρ) k = F (lookupᴾ ρ k)

εᴾ : All 𝓟 [] (([] ─Env) T Δ ∋ ε)
lookupᴾ εᴾ ()

infixl 20 _∙ᴾ_
_∙ᴾ_ : ∀ {ρ : (Γ ─Env) T Δ} {v : T σ Δ} → All 𝓟 Γ ρ → pred 𝓟 σ v → All 𝓟 (σ ∷ Γ) (ρ ∙ v)
lookupᴾ (ρ ∙ᴾ v) z      = v
lookupᴾ (ρ ∙ᴾ v) (s k)  = lookupᴾ ρ k
\end{code}

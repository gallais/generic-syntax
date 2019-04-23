\begin{code}
{-# OPTIONS --safe #-}

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
  field pred : ∀[ T σ ⇒ const Set ]
open Pred public

record All (Γ : List I) (𝓟 : Pred T) (ρ : (Γ ─Env) T Δ) : Set where
  constructor pack^P
  field lookup^P : (k : Var σ Γ) → pred 𝓟 (lookup ρ k)
open All public

private
  variable
    𝓟 : Pred T

_<$>^P_ : {f : {i : I} → T i Δ → T i Θ} →
          (∀ {i} {t : T i Δ} → pred 𝓟 t → pred 𝓟 (f t)) →
          {ρ : (Γ ─Env) T Δ} → All Γ 𝓟 ρ → All Γ 𝓟 (f <$> ρ)
lookup^P (F <$>^P ρ) k = F (lookup^P ρ k)

ε^P : All [] 𝓟 (([] ─Env) T Δ ∋ ε)
lookup^P ε^P ()

infixl 20 _∙^P_
_∙^P_ :  {ρ : (Γ ─Env) T Δ} → All Γ 𝓟 ρ →
         {v : T σ Δ} → pred 𝓟 v → All (σ ∷ Γ) 𝓟 (ρ ∙ v)
lookup^P (ρ ∙^P v) z      = v
lookup^P (ρ ∙^P v) (s k)  = lookup^P ρ k
\end{code}

module pred where

open import indexed
open import var hiding (_<$>_)
open import environment
open import Agda.Builtin.List

record Pred {I : Set} (T : I ─Scoped) : Set₁ where
  constructor mkPred
  field pred : {i : I} → [ T i ⟶ κ Set ]
open Pred public

module _ {I : Set} {T : I ─Scoped} where

 record ∀[_] (𝓟 : Pred T) {Γ Δ : List I} (ρ : (Γ ─Env) T Δ) : Set where
   constructor pack^P
   field lookup^P : ∀ {i} k → pred 𝓟 {i} (lookup ρ k)
 open ∀[_] public

module _ {I : Set} {T : I ─Scoped} {𝓟 : Pred T} where

 _<$>^P_ : {Γ Δ Θ : List I} {f : {i : I} → T i Δ → T i Θ} →
           ({i : I} {t : T i Δ} → pred 𝓟 t → pred 𝓟 (f t)) →
           {ρ : (Γ ─Env) T Δ} → ∀[ 𝓟 ] ρ → ∀[ 𝓟 ] (f <$> ρ)
 lookup^P (F <$>^P ρ) k = F (lookup^P ρ k)

module _ {I : Set} {T : I ─Scoped} {𝓟 : Pred T} {Δ : List I} where

 ε^P : ∀[ 𝓟 ] (ε {n = Δ})
 lookup^P ε^P ()

module _ {I : Set} {T : I ─Scoped} {𝓟 : Pred T} {Γ Δ : List I} where

 infixl 20 _∙^P_
 _∙^P_ :  {ρ : (Γ ─Env) T Δ} → ∀[ 𝓟 ] ρ → {i : I} {v : T i Δ} → pred 𝓟 v → ∀[ 𝓟 ] (ρ ∙ v)
 lookup^P (ρ ∙^P v) z      = v
 lookup^P (ρ ∙^P v) (s k)  = lookup^P ρ k




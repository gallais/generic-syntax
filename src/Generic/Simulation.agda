module Generic.Simulation where

open import Size
open import Data.List hiding ([_] ; lookup ; zip)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import indexed
open import var hiding (_<$>_)
open import varlike
open import rel
open import environment
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Zip

module _ {I : Set} {𝓥₁ 𝓥₂ 𝓒₁ 𝓒₂ : I → List I → Set} (𝓡^𝓥  : Rel 𝓥₁ 𝓥₂) (𝓡^𝓒  : Rel 𝓒₁ 𝓒₂) where

 reify^R : {vl₁ : VarLike 𝓥₁} {vl₂ : VarLike 𝓥₂} (vl^R : VarLike^R 𝓡^𝓥 vl₁ vl₂) →
           {Γ : List I} → ∀ Δ σ → {k₁ : Kripke 𝓥₁ 𝓒₁ Δ σ Γ} {k₂ : Kripke 𝓥₂ 𝓒₂ Δ σ Γ} →
           Kripke^R 𝓡^𝓥 𝓡^𝓒 Δ σ k₁ k₂ → rel 𝓡^𝓒 (reify vl₁ Δ σ k₁) (reify vl₂ Δ σ k₂)
 reify^R vl^R []         σ k^R = k^R
 reify^R vl^R Δ@(_ ∷ _)  σ k^R = k^R (freshʳ vl^Var Δ) (VarLike^R.freshˡ^R vl^R _)

 record Sim (d : Desc I) (𝓢₁ : Sem d 𝓥₁ 𝓒₁) (𝓢₂ : Sem d 𝓥₂ 𝓒₂) : Set where
   field  th^R   : {Γ Δ : List I} {i : I} {v₁ : 𝓥₁ i Γ} {v₂ : 𝓥₂ i Γ} → (σ : Thinning Γ Δ) → rel 𝓡^𝓥 v₁ v₂ → rel 𝓡^𝓥 (Sem.th^𝓥 𝓢₁ v₁ σ) (Sem.th^𝓥 𝓢₂ v₂ σ)
          var^R  : {Γ : List I} {i : I} {v₁ : 𝓥₁ i Γ} {v₂ : 𝓥₂ i Γ} → rel 𝓡^𝓥 v₁ v₂ → rel 𝓡^𝓒 (Sem.var 𝓢₁ v₁) (Sem.var 𝓢₂ v₂)
          alg^R  :  {Γ Δ : List I} {i : I} {s : Size} → (b : ⟦ d ⟧ (Scope (Tm d s)) i Γ) → {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Γ ─Env) 𝓥₂ Δ} → ∀[ 𝓡^𝓥 ] ρ₁ ρ₂ →
                    let  v₁ = fmap d (Sem.body 𝓢₁ ρ₁) b
                         v₂ = fmap d (Sem.body 𝓢₂ ρ₂) b
                    in Zip d (Kripke^R 𝓡^𝓥 𝓡^𝓒) v₁ v₂ → rel 𝓡^𝓒 (Sem.alg 𝓢₁ v₁) (Sem.alg 𝓢₂ v₂)

   sim   :  {Γ Δ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Γ ─Env) 𝓥₂ Δ} {i : I} {s : Size} → ∀[ 𝓡^𝓥 ] ρ₁ ρ₂ → (t : Tm d s i Γ) → rel 𝓡^𝓒 (Sem.sem 𝓢₁ ρ₁ t) (Sem.sem 𝓢₂ ρ₂ t)
   body  :  {Γ Θ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Θ} {ρ₂ : (Γ ─Env) 𝓥₂ Θ} {s : Size} → ∀[ 𝓡^𝓥 ] ρ₁ ρ₂ → ∀ Δ j → (t : Scope (Tm d s) Δ j Γ) →
            Kripke^R 𝓡^𝓥 𝓡^𝓒 Δ j (Sem.body 𝓢₁ ρ₁ Δ j t) (Sem.body 𝓢₂ ρ₂ Δ j t)

   sim ρ (`var k) = var^R (lookup^R ρ k)
   sim ρ (`con t) = alg^R t ρ (zip d (body ρ) t)

   body ρ []       i t = sim ρ t
   body ρ (σ ∷ Δ)  i t = λ σ ρ′ → sim (ρ′ >>^R (th^R σ <$>^R ρ)) t

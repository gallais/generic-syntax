\begin{code}
module Generic.Fundamental where

open import Size
open import Agda.Builtin.List
open import Data.Unit
open import Data.Product

open import indexed
open import var
open import pred as P hiding (∀[_])
open import rel  as R hiding (∀[_])
open import varlike
open import environment
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Unit
open import Generic.Zip
open import Generic.Simulation

module _ {I : Set} {T : I ─Scoped} where

  fromPred : Pred T → Rel T Unit
  rel (fromPred T^P) = λ t _ → pred T^P t

  fromPred∀ : ∀ {T^P : Pred T} {Γ Δ} {ρ : (Γ ─Env) T Δ} {ρ′} → P.∀[ T^P ] ρ → R.∀[ fromPred T^P ] ρ ρ′
  lookup^R (fromPred∀ ρ^P) k = lookup^P ρ^P k

  fromRel∀ : ∀ {T^P : Pred T} {Γ Δ} {ρ : (Γ ─Env) T Δ} {ρ′} → R.∀[ fromPred T^P ] ρ ρ′ → P.∀[ T^P ] ρ
  lookup^P (fromRel∀ ρ^R) k = lookup^R ρ^R k

module _ {I : Set} {X : List I → I ─Scoped} where

 All : ∀ (d : Desc I) (X^P : ∀ Δ i → [ X Δ i ⟶ κ Set ]) {i Γ} (v : ⟦ d ⟧ X i Γ) → Set
 All (`σ A d)   X^P (a , v) = All (d a) X^P v
 All (`X Δ j d) X^P (r , v) = X^P Δ j r × All d X^P v
 All (`∎ i)     X^P v       = ⊤


module _ {I : Set} {𝓥 𝓒 : I ─Scoped} (𝓥^P : Pred 𝓥) (𝓒^P : Pred 𝓒) where

 fromKripke^R : ∀ Δ j {Γ k₂} {k₁ : Kripke 𝓥 𝓒 Δ j Γ} →
                Kripke^R (fromPred 𝓥^P) (fromPred 𝓒^P) Δ j k₁ k₂ → Kripke^P 𝓥^P 𝓒^P Δ j k₁
 fromKripke^R []        j k^R = k^R
 fromKripke^R Δ@(_ ∷ _) j k^R = λ ρ vs^P → k^R ρ (fromPred∀ vs^P)

 fromZip : ∀ (d : Desc I) {i Γ} {v : ⟦ d ⟧ (Kripke 𝓥 𝓒) i Γ} {w : ⟦ d ⟧ (Kripke Unit Unit) i Γ} →
           Zip d (Kripke^R (fromPred 𝓥^P) (fromPred 𝓒^P)) v w → All d (Kripke^P 𝓥^P 𝓒^P) v
 fromZip (`σ A d)   (_ , v) = fromZip (d _) v
 fromZip (`X Δ j d) (r , v) = fromKripke^R Δ j r , fromZip d v
 fromZip (`∎ eq)    _       = _

 record Fdm (d : Desc I) (𝓢 : Sem d 𝓥 𝓒) : Set where
   field th^P  : ∀ {i Γ Δ} {v : 𝓥 i Γ} (ρ : Thinning Γ Δ) → pred 𝓥^P v → pred 𝓥^P (Sem.th^𝓥 𝓢 v ρ)
         var^P : ∀ {i Γ} {v : 𝓥 i Γ} → pred 𝓥^P v → pred 𝓒^P (Sem.var 𝓢 v)
         alg^P : ∀ {i s Γ Δ} (b : ⟦ d ⟧ (Scope (Tm d s)) i Γ) {ρ : (Γ ─Env) 𝓥 Δ} (ρ^P : P.∀[ 𝓥^P ] ρ) →
                 let v = fmap d (Sem.body 𝓢 ρ) b in All d (Kripke^P 𝓥^P 𝓒^P) v → pred 𝓒^P (Sem.alg 𝓢 v)

   sim : Sim (fromPred 𝓥^P) (fromPred 𝓒^P) d 𝓢 SemUnit
   Sim.th^R   sim = th^P
   Sim.var^R  sim = var^P
   Sim.alg^R  sim = λ b ρ^R zp → alg^P b (fromRel∀ ρ^R) (fromZip d zp)

   fdm : ∀ {i Γ Δ} {ρ : (Γ ─Env) 𝓥 Δ} → P.∀[ 𝓥^P ] ρ → (t : Tm d ∞ i Γ) → pred 𝓒^P (Sem.sem 𝓢 ρ t)
   fdm ρ^P t = Sim.sim sim (fromPred∀ ρ^P) t
\end{code}

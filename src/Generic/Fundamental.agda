{-# OPTIONS --safe --sized-types #-}

module Generic.Fundamental where

open import Size
open import Agda.Builtin.List
open import Data.Unit
open import Data.Product
open import Function
open import Relation.Unary hiding (Pred)
open import Relation.Binary.PropositionalEquality

open import Data.Var
open import Data.Pred     as P using (Pred; pred; lookupᴾ)
open import Data.Relation as R using (Rel; rel; lookupᴿ)
open import Data.Var.Varlike
open import Data.Environment
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Unit
open import Generic.Relator
open import Generic.Simulation

private
  variable
    I : Set
    i : I
    Γ Δ : List I
    T 𝓥 𝓒 : I ─Scoped
    Tᴾ : Pred T
    X : List I → I ─Scoped

fromPred : Pred {I} T → Rel T Unit
rel (fromPred Tᴾ) = λ σ t _ → pred Tᴾ σ t

fromPred∀ : ∀ {ρ : (Γ ─Env) T Δ} {ρ′} → P.All Tᴾ _ ρ → R.All (fromPred Tᴾ) _ ρ ρ′
lookupᴿ (fromPred∀ ρᴾ) k = lookupᴾ ρᴾ k

fromRel∀ : ∀ {ρ : (Γ ─Env) T Δ} {ρ′} → R.All (fromPred Tᴾ) _ ρ ρ′ → P.All Tᴾ _ ρ
lookupᴾ (fromRel∀ ρᴿ) k = lookupᴿ ρᴿ k

All : (d : Desc I) (Xᴾ : ∀ Δ i → ∀[ X Δ i ⇒ const Set ]) (v : ⟦ d ⟧ X i Γ) → Set
All (`σ A d)   Xᴾ (a , v) = All (d a) Xᴾ v
All (`X Δ j d) Xᴾ (r , v) = Xᴾ Δ j r × All d Xᴾ v
All (`∎ i)     Xᴾ v       = ⊤


module _ (𝓥ᴾ : Pred {I} 𝓥) (𝓒ᴾ : Pred {I} 𝓒) where

 fromKripkeᴿ : ∀ Δ j {k₂} {k₁ : Kripke 𝓥 𝓒 Δ j Γ} →
               Kripkeᴿ (fromPred 𝓥ᴾ) (fromPred 𝓒ᴾ) Δ j k₁ k₂ → Kripkeᴾ 𝓥ᴾ 𝓒ᴾ Δ j k₁
 fromKripkeᴿ []        j kᴿ = kᴿ
 fromKripkeᴿ Δ@(_ ∷ _) j kᴿ = λ ρ vsᴾ → kᴿ ρ (fromPred∀ vsᴾ)

 fromRelator : ∀ (d : Desc I) {v : ⟦ d ⟧ (Kripke 𝓥 𝓒) i Γ} {w : ⟦ d ⟧ (Kripke Unit Unit) i Γ} →
           ⟦ d ⟧ᴿ (Kripkeᴿ (fromPred 𝓥ᴾ) (fromPred 𝓒ᴾ)) v w → All d (Kripkeᴾ 𝓥ᴾ 𝓒ᴾ) v
 fromRelator (`σ A d)    (refl , v)  = fromRelator (d _) v
 fromRelator (`X Δ j d)  (r , v)     = fromKripkeᴿ Δ j r , fromRelator d v
 fromRelator (`∎ eq)     _           = _

record Fundamental
       (d : Desc I) (𝓢 : Semantics d 𝓥 𝓒)
       (𝓥ᴾ : Pred 𝓥) (𝓒ᴾ : Pred 𝓒): Set where
  module 𝓢 = Semantics 𝓢
  field thᴾ  : ∀ {v} (ρ : Thinning Γ Δ) → pred 𝓥ᴾ i v → pred 𝓥ᴾ i (𝓢.th^𝓥 v ρ)
        varᴾ : ∀ {v : 𝓥 i Γ} → pred 𝓥ᴾ i v → pred 𝓒ᴾ i (𝓢.var v)
        algᴾ : ∀ {s}  {ρ : (Γ ─Env) 𝓥 Δ}
               (b : ⟦ d ⟧ (Scope (Tm d s)) i Γ) → let v = fmap d (Semantics.body 𝓢 ρ) b in
               (ρᴾ : P.All 𝓥ᴾ _ ρ) →
               All d (Kripkeᴾ 𝓥ᴾ 𝓒ᴾ) v → pred 𝓒ᴾ i (𝓢.alg v)

  sim : Simulation d 𝓢 SemUnit (fromPred 𝓥ᴾ) (fromPred 𝓒ᴾ)
  Simulation.thᴿ   sim = thᴾ
  Simulation.varᴿ  sim = varᴾ
  Simulation.algᴿ  sim = λ b ρᴿ zp → algᴾ b (fromRel∀ ρᴿ) (fromRelator _ _ d zp)

  fundamental : ∀ {s} {ρ : (Γ ─Env) 𝓥 Δ} → P.All 𝓥ᴾ _ ρ →
                (t : Tm d s i Γ) → pred 𝓒ᴾ i (Semantics.semantics 𝓢 ρ t)
  fundamental ρᴾ t = Simulation.sim sim (fromPred∀ ρᴾ) t

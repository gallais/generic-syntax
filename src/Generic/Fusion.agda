{-# OPTIONS --safe --sized-types #-}

open import Data.Var hiding (z; s; _<$>_)

module Generic.Fusion {I : Set} {𝓥ᴬ 𝓥ᴮ 𝓥ᴬᴮ 𝓒ᴬ 𝓒ᴮ 𝓒ᴬᴮ : I ─Scoped} where

open import Size
open import Data.List hiding ([_] ; zip ; lookup)
open import Function renaming (_∘′_ to _∘_) hiding (_∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Relation.Unary
open import Data.Relation hiding (_>>ᴿ_)
open import Data.Var.Varlike
open import Data.Environment

open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Relator

private
  variable
    s : Size
    σ τ : I
    Γ Δ Θ Ω : List I
    ρᴬ : (Γ ─Env) 𝓥ᴬ Δ
    ρᴮ : (Δ ─Env) 𝓥ᴮ Θ
    ρᴬᴮ : (Γ ─Env) 𝓥ᴬᴮ Θ
    vsᴬᴮ : (Δ ─Env) 𝓥ᴬᴮ Γ
    vsᴮ : (Δ ─Env) 𝓥ᴮ Γ


record Fusion (d : Desc I) (𝓢ᴬ : Semantics d 𝓥ᴬ 𝓒ᴬ) (𝓢ᴮ : Semantics d 𝓥ᴮ 𝓒ᴮ)
  (𝓢ᴬᴮ : Semantics d 𝓥ᴬᴮ 𝓒ᴬᴮ)
  (𝓔ᴿ : ∀ Γ Δ {Θ} → (Γ ─Env) 𝓥ᴬ Δ → (Δ ─Env) 𝓥ᴮ Θ → (Γ ─Env) 𝓥ᴬᴮ Θ → Set)
  (𝓥ᴿ : Rel 𝓥ᴮ 𝓥ᴬᴮ) (𝓒ᴿ : Rel 𝓒ᴮ 𝓒ᴬᴮ) : Set where

  module 𝓢ᴬ = Semantics 𝓢ᴬ
  module 𝓢ᴮ = Semantics 𝓢ᴮ
  module 𝓢ᴬᴮ = Semantics 𝓢ᴬᴮ
  evalᴬ = 𝓢ᴬ.semantics
  evalᴮ = 𝓢ᴮ.semantics
  evalᴬᴮ = 𝓢ᴬᴮ.semantics
  field

    reifyᴬ  :  ∀ σ → ∀[ 𝓒ᴬ σ ⇒ Tm d ∞ σ ]

    vl^𝓥ᴬ :  VarLike 𝓥ᴬ

  quoteᴬ : ∀ Δ i → Kripke 𝓥ᴬ 𝓒ᴬ Δ i Γ → Tm d ∞ i (Δ ++ Γ)
  quoteᴬ Δ i k = reifyᴬ i (reify vl^𝓥ᴬ Δ i k)

  field

    _>>ᴿ_  :  𝓔ᴿ Γ Δ ρᴬ ρᴮ ρᴬᴮ → All 𝓥ᴿ Θ vsᴮ vsᴬᴮ →
              let id>>ρᴬ = freshˡ vl^𝓥ᴬ Δ >> th^Env 𝓢ᴬ.th^𝓥 ρᴬ (freshʳ vl^Var Θ)
              in 𝓔ᴿ (Θ ++ Γ) (Θ ++ Δ) id>>ρᴬ (vsᴮ >> ρᴮ) (vsᴬᴮ >> ρᴬᴮ)

    th^𝓔ᴿ  : 𝓔ᴿ Γ Δ ρᴬ ρᴮ ρᴬᴮ  → (ρ : Thinning Θ Ω) →
             𝓔ᴿ Γ Δ ρᴬ (th^Env 𝓢ᴮ.th^𝓥 ρᴮ ρ) (th^Env 𝓢ᴬᴮ.th^𝓥 ρᴬᴮ ρ)

  𝓡 :  ∀ σ → (Γ ─Env) 𝓥ᴬ Δ → (Δ ─Env) 𝓥ᴮ Θ → (Γ ─Env) 𝓥ᴬᴮ Θ →
       Tm d s σ Γ → Set
  𝓡 σ ρᴬ ρᴮ ρᴬᴮ t = rel 𝓒ᴿ σ (evalᴮ ρᴮ (reifyᴬ σ (evalᴬ ρᴬ t))) (evalᴬᴮ ρᴬᴮ t)

  field

    varᴿ : 𝓔ᴿ Γ Δ ρᴬ ρᴮ ρᴬᴮ → ∀ v → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ (`var v)

    algᴿ : 𝓔ᴿ Γ Δ ρᴬ ρᴮ ρᴬᴮ → (b : ⟦ d ⟧ (Scope (Tm d s)) σ Γ) →
           let  bᴬ :  ⟦ d ⟧ (Kripke 𝓥ᴬ 𝓒ᴬ) _ _
                bᴬ   = fmap d (𝓢ᴬ.body ρᴬ) b
                bᴮ   = fmap d (λ Δ i → 𝓢ᴮ.body ρᴮ Δ i ∘ quoteᴬ Δ i) bᴬ
                bᴬᴮ  = fmap d (𝓢ᴬᴮ.body ρᴬᴮ) b
           in ⟦ d ⟧ᴿ (Kripkeᴿ 𝓥ᴿ 𝓒ᴿ) bᴮ bᴬᴮ → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ (`con b)

  fusion : 𝓔ᴿ Γ Δ ρᴬ ρᴮ ρᴬᴮ → (t : Tm d s σ Γ) → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ t

  body   : 𝓔ᴿ Γ Δ ρᴬ ρᴮ ρᴬᴮ → ∀ Δ σ → (b : Scope (Tm d s) Δ σ Γ) →
           let vᴮ   = 𝓢ᴮ.body ρᴮ Δ σ (quoteᴬ Δ σ (𝓢ᴬ.body ρᴬ Δ σ b))
               vᴬᴮ  = 𝓢ᴬᴮ.body ρᴬᴮ Δ σ b
           in Kripkeᴿ 𝓥ᴿ 𝓒ᴿ Δ σ vᴮ vᴬᴮ

  fusion ρᴿ (`var v) = varᴿ ρᴿ v
  fusion ρᴿ (`con t) = algᴿ ρᴿ t (rew (liftᴿ d (body ρᴿ) t)) where

     eq  = fmap² d (𝓢ᴬ.body _) (λ Δ i t → 𝓢ᴮ.body _ Δ i (quoteᴬ Δ i t)) t
     rew = subst (λ v → ⟦ d ⟧ᴿ (Kripkeᴿ 𝓥ᴿ 𝓒ᴿ) v _) (sym eq)

  body ρᴿ []       i b = fusion ρᴿ b
  body ρᴿ (σ ∷ Δ)  i b = λ ρ vsᴿ → fusion (th^𝓔ᴿ ρᴿ ρ >>ᴿ vsᴿ) b

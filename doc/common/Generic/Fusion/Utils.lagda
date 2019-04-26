\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Fusion.Utils where

open import Data.Var hiding (_<$>_)

open import Size
open import Data.List hiding ([_] ; zip ; lookup)
open import Function renaming (_∘′_ to _∘_) hiding (_∘_)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Relation hiding (_>>ᴿ_)
open import Data.Var.Varlike
open import Data.Environment

open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Fusion

module _ {I : Set} {T : I ─Scoped} where

  open ≡-Reasoning

  -- this is the shape of environment one obtains when pushing an evaluation environment
  -- on top of a thinning into the body of a binder

  thBodyEnv :
    ∀ {Γ Δ Θ Ξ : List I} {ρᴬ : Thinning Γ Δ} {ρᴮ : (Δ ─Env) T Θ}
    {ρᴬᴮ : (Γ ─Env) T Θ} {ρ₄ ρ₅ : (Ξ ─Env) T Θ}
    (ρᴿ : All Eqᴿ Γ (select ρᴬ ρᴮ) ρᴬᴮ) (vsᴿ : All Eqᴿ Ξ ρ₄ ρ₅) →
    let σ : (Ξ ++ Γ ─Env) Var (Ξ ++ Δ)
        σ = freshˡ vl^Var Δ >> th^Env th^Var ρᴬ (freshʳ vl^Var Ξ)
    in All Eqᴿ (Ξ ++ Γ) (select σ (ρ₄ >> ρᴮ)) (ρ₅ >> ρᴬᴮ)
  lookupᴿ (thBodyEnv {Γ} {Δ} {Θ} {Ξ} {ρᴬ} {ρᴮ} {ρᴬᴮ} {ρ₄} {ρ₅} ρᴿ vsᴿ) k
    with split Ξ k
  ... | inj₁ kˡ = begin
    lookup (ρ₄ >> ρᴮ) (injectˡ Δ (lookup (base vl^Var) kˡ))
      ≡⟨ injectˡ->> ρ₄ ρᴮ (lookup (base vl^Var) kˡ) ⟩
    lookup ρ₄ (lookup (base vl^Var) kˡ)
      ≡⟨ cong (lookup ρ₄) (lookup-base^Var kˡ) ⟩
    lookup ρ₄ kˡ
      ≡⟨ lookupᴿ vsᴿ kˡ ⟩
    lookup ρ₅ kˡ
      ∎
  ... | inj₂ kʳ = begin
    lookup (ρ₄ >> ρᴮ) (injectʳ Ξ (lookup (base vl^Var) (lookup ρᴬ kʳ)))
      ≡⟨ injectʳ->> ρ₄ ρᴮ (lookup (base vl^Var) (lookup ρᴬ kʳ)) ⟩
    lookup ρᴮ (lookup (base vl^Var) (lookup ρᴬ kʳ))
      ≡⟨ cong (lookup ρᴮ) (lookup-base^Var (lookup ρᴬ kʳ)) ⟩
    lookup ρᴮ (lookup ρᴬ kʳ)
      ≡⟨ lookupᴿ ρᴿ kʳ ⟩
    lookup ρᴬᴮ kʳ
      ∎

module _ {I : Set} {d : Desc I}  {𝓥 𝓒 : I ─Scoped}
         (𝓢 : Semantics d 𝓥 𝓒)
         (𝓕 : Fusion d Ren 𝓢 𝓢 (λ Γ Δ ρᴬ ρᴮ → All Eqᴿ _ (select ρᴬ ρᴮ)) Eqᴿ Eqᴿ)
         (eq^quote : ∀ σ {Γ} (t : Tm d ∞ σ Γ) → Fusion.reifyᴬ 𝓕 σ t ≡ t) where

  open ≡-Reasoning
  module 𝓢 = Semantics 𝓢

  SemVarTmᴿ : Rel 𝓥 𝓒
  rel SemVarTmᴿ σ v c = 𝓢.var v ≡ c

  -- this is the shape of environment one obtains when pushing an evaluation environment
  -- on top of a substitution into the body of a binder

  subBodyEnv :
    ∀ {Γ Δ Θ Ξ} (ρᴬ : (Γ ─Env) (Tm d _) Δ) {ρᴮ : (Δ ─Env) 𝓥 Θ} {ρᴬᴮ}
    {ρ₄ : (Ξ ─Env) 𝓥 Θ} {ρ₅ : (Ξ ─Env) 𝓒 Θ} →
    All Eqᴿ Γ (𝓢.semantics ρᴮ <$> ρᴬ) ρᴬᴮ →
    All SemVarTmᴿ _  ρ₄ ρ₅ →
    let σ : ((Ξ ++ Γ) ─Env) (Tm d _) (Ξ ++ Δ)
        σ = freshˡ vl^Tm Δ >> th^Env th^Tm ρᴬ (freshʳ vl^Var Ξ)
    in All Eqᴿ (Ξ ++ Γ) (𝓢.semantics (ρ₄ >> ρᴮ) <$> σ) (ρ₅ >> ρᴬᴮ)
  lookupᴿ (subBodyEnv {Γ} {Δ} {Θ} {Ξ} ρᴬ {ρᴮ} {ρᴬᴮ} {ρ₄} {ρ₅} ρᴿ vsᴿ) k
    with split Ξ k
  ... | inj₁ kˡ = begin
    let t = ren (pack (injectˡ Δ)) (lookup (base vl^Tm) kˡ) in
    𝓢.semantics (ρ₄ >> ρᴮ) t
      ≡⟨ cong (𝓢.semantics (ρ₄ >> ρᴮ)) (sym (eq^quote _ t)) ⟩
    𝓢.semantics (ρ₄ >> ρᴮ) (Fusion.reifyᴬ 𝓕 _ t)
      ≡⟨ Fusion.fusion 𝓕 (packᴿ (injectˡ->> ρ₄ ρᴮ)) (lookup (base vl^Tm) kˡ) ⟩
    𝓢.semantics ρ₄ (lookup (base vl^Tm) kˡ)
      ≡⟨ cong (𝓢.semantics ρ₄) (lookup-base^Tm kˡ) ⟩
    𝓢.var(lookup ρ₄ kˡ)
      ≡⟨ lookupᴿ vsᴿ kˡ ⟩
    lookup ρ₅ kˡ
      ∎
  ... | inj₂ kʳ = begin
    let t = ren (freshʳ vl^Var Ξ) (lookup ρᴬ kʳ) in
    𝓢.semantics (ρ₄ >> ρᴮ) t
      ≡⟨ cong (𝓢.semantics (ρ₄ >> ρᴮ)) (sym (eq^quote _ t)) ⟩
    𝓢.semantics (ρ₄ >> ρᴮ) (Fusion.reifyᴬ 𝓕 _ t)
      ≡⟨ Fusion.fusion 𝓕 eqᴿ (lookup ρᴬ kʳ) ⟩
    𝓢.semantics ρᴮ (lookup ρᴬ kʳ)
      ≡⟨ lookupᴿ ρᴿ kʳ ⟩
    lookup ρᴬᴮ kʳ
      ∎ where

    eqᴿ : All Eqᴿ Δ (select (freshʳ vl^Var Ξ) (ρ₄ >> ρᴮ)) ρᴮ
    lookupᴿ eqᴿ v = begin
      lookup (select (freshʳ vl^Var Ξ) (ρ₄ >> ρᴮ)) v
        ≡⟨ injectʳ->> ρ₄ ρᴮ (lookup (base vl^Var) v) ⟩
      lookup ρᴮ (lookup (base vl^Var) v)
        ≡⟨ cong (lookup ρᴮ) (lookup-base^Var v) ⟩
      lookup ρᴮ v
        ∎
\end{code}

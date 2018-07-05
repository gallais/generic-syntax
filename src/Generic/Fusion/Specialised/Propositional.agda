--------------------------------------------------------------------------------
-- This is the closest one can come to an axiom-free verison of Kaiser, Schäfer,
-- and Stark's observation that our notion of Semantics is intrinsically able to
-- absord any Renaming which may have come before.
--
-- This is used both to replicate Kaiser, Schäfer, and Stark's result in the
-- module Generic.Fusion.Specialised and to make the fusion proofs of renaming
-- with renaming, substitution, and let-elaboration simpler.
--------------------------------------------------------------------------------

module Generic.Fusion.Specialised.Propositional where

open import indexed
open import var hiding (_<$>_)
open import environment
open import varlike
open import rel
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Zip
open import Generic.Fusion
open import Generic.Identity

open import Size
open import Function
open import Data.Sum
open import Data.Product hiding (,_)
open import Data.List.Base hiding (lookup)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

module _ {I} (d : Desc I) {𝓥 𝓒} (S : Sem d 𝓥 𝓒)
         (alg-fusion :
            ∀ {i σ Γ Δ Θ} (b : ⟦ d ⟧ (Scope (Tm d i)) σ Γ) {ρ₁ ρ₃} {ρ₂ : (Δ ─Env) 𝓥 Θ} →
            ∀[ Eq^R ] (select ρ₁ ρ₂) ρ₃ →
            let f = λ Δ σ → Sem.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ ∘ Sem.body Renaming ρ₁ Δ σ
                g = Sem.body S ρ₃
            in Zip d (Kripke^R Eq^R Eq^R) (fmap d f b) (fmap d g b) →
            Sem.alg S (fmap d f b) ≡ Sem.alg S (fmap d g b))
        where

  ren-sem : Fus (λ σ → ∀[ Eq^R ] ∘ (select σ)) Eq^R Eq^R d Renaming S S
  Fus.quote₁ ren-sem = λ _ t → t
  Fus.vl^𝓥₁ ren-sem = vl^Var
  Fus.th^R   ren-sem = λ σ ρ^R → pack^R (λ v → cong (λ ρ → Sem.th^𝓥 S ρ σ) (lookup^R ρ^R v))
  lookup^R (Fus.>>^R ren-sem {Γ} {Δ} {Θ} {Ξ} {σ} {ρ₁} {ρ₂} {vs} {ws} ρ^R vs^R) v with split Ξ v
  ... | inj₁ vˡ = begin
    lookup (vs >> ρ₁) (injectˡ Δ (lookup (base vl^Var) vˡ))
      ≡⟨ injectˡ->> vs ρ₁ (lookup (base vl^Var) vˡ) ⟩
    lookup vs (lookup (base vl^Var) vˡ)
      ≡⟨ cong (lookup vs) (lookup-base^Var vˡ) ⟩
    lookup vs vˡ
      ≡⟨ lookup^R vs^R vˡ ⟩
    lookup ws vˡ
      ∎
  ... | inj₂ vʳ = begin
    lookup (vs >> ρ₁) (injectʳ Ξ (lookup (base vl^Var) (lookup σ vʳ)))
      ≡⟨ injectʳ->> vs ρ₁ (lookup (base vl^Var) (lookup σ vʳ)) ⟩
    lookup ρ₁ (lookup (base vl^Var) (lookup σ vʳ))
      ≡⟨ cong (lookup ρ₁) (lookup-base^Var (lookup σ vʳ)) ⟩
    lookup ρ₁ (lookup σ vʳ)
      ≡⟨ lookup^R ρ^R vʳ ⟩
    lookup ρ₂ vʳ
      ∎
  Fus.var^R  ren-sem = λ ρ^R v → cong (Sem.var S) (lookup^R ρ^R v)
  Fus.alg^R  ren-sem {Γ} {Δ} {σ} {si} {ρ₁ = ρ₁} {ρ₂} {ρ₃} b ρ^R zp = begin
    Sem.alg S (fmap d (Sem.body S ρ₂) (fmap d (reify vl^Var) v₁))
      ≡⟨ cong (Sem.alg S) (fmap² d (reify vl^Var) (Sem.body S ρ₂) (fmap d (Sem.body Renaming ρ₁) b)) ⟩
    Sem.alg S (fmap d (λ Δ σ → Sem.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ) (fmap d (Sem.body Renaming ρ₁) b))
      ≡⟨ cong (Sem.alg S) aux ⟩
    Sem.alg S (fmap d (λ Δ σ → Sem.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ ∘ Sem.body Renaming ρ₁ Δ σ) b)
      ≡⟨ alg-fusion b ρ^R (subst (λ t → Zip d _ t v₃) aux zp) ⟩
    Sem.alg S v₃
      ∎ where

      rew = λ {σ Γ} (t : ⟦ d ⟧ (Scope (Tm d ∞)) σ Γ) →
              `con-inj {I} {σ} {Γ} {d} (≅⇒≡ (RenId.ren-id (`con t) (pack^R λ _ → refl)))
      v₁  = fmap d (Sem.body Renaming ρ₁) b
      v₃  = fmap d (Sem.body S ρ₃) b

      aux : fmap d (λ Δ σ → Sem.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ) v₁
          ≡ fmap d (λ Δ σ → Sem.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ ∘ Sem.body Renaming ρ₁ Δ σ) b
      aux = begin
        fmap d (λ Δ σ → Sem.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ) v₁
          ≡⟨ fmap² d (Sem.body Renaming ρ₁) (λ Δ σ → Sem.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ) b ⟩
        fmap d (λ Δ σ → Sem.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ ∘ Sem.body Renaming ρ₁ Δ σ) b
          ∎

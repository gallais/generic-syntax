\begin{code}
--------------------------------------------------------------------------------
-- This is the closest one can come to an axiom-free verison of Kaiser, Schäfer,
-- and Stark's observation that our notion of Semantics is intrinsically able to
-- absord any Renaming which may have come before.
--
-- This is used both to replicate Kaiser, Schäfer, and Stark's result in the
-- module Generic.Fusion.Specialised and to make the fusion proofs of renaming
-- with renaming, substitution, and let-elaboration simpler.
--------------------------------------------------------------------------------

{-# OPTIONS --safe --sized-types #-}

module Generic.Fusion.Specialised.Propositional where

open import Relation.Unary
open import Data.Var hiding (_<$>_)
open import Data.Environment
open import Data.Var.Varlike
open import Data.Relation
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Relator
open import Generic.Fusion
open import Generic.Identity

open import Size
open import Function
open import Data.Sum
open import Data.Product
open import Data.List.Base hiding (lookup)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

module _ {I} (d : Desc I) {𝓥 𝓒} (S : Semantics d 𝓥 𝓒)
         (alg-fusion :
            ∀ {i σ Γ Δ Θ} (b : ⟦ d ⟧ (Scope (Tm d i)) σ Γ) {ρ₁ ρ₃} {ρ₂ : (Δ ─Env) 𝓥 Θ} →
            All Eqᴿ _ (select ρ₁ ρ₂) ρ₃ →
            let f = λ Δ σ → Semantics.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ ∘ Semantics.body Ren ρ₁ Δ σ
                g = Semantics.body S ρ₃
            in ⟦ d ⟧ᴿ (Kripkeᴿ Eqᴿ Eqᴿ) (fmap d f b) (fmap d g b) →
            Semantics.alg S (fmap d f b) ≡ Semantics.alg S (fmap d g b))
        where

  module Ren = Semantics (Ren {d = d})

  ren-sem : Fusion d Ren S S (λ Γ Δ σ → All Eqᴿ Γ ∘ (select σ)) Eqᴿ Eqᴿ
  Fusion.reifyᴬ ren-sem = λ _ t → t
  Fusion.vl^𝓥ᴬ ren-sem = vl^Var
  Fusion.th^𝓔ᴿ   ren-sem = λ ρᴿ σ → packᴿ (λ v → cong (λ ρ → Semantics.th^𝓥 S ρ σ) (lookupᴿ ρᴿ v))
  lookupᴿ (Fusion._>>ᴿ_ ren-sem {Γ} {Δ} {ρ₁} {Ω} {ρ₂} {ρ₃} {Θ} {vs} {ws} ρᴿ vsᴿ) v with split Θ v
  ... | inj₁ vˡ = begin
    lookup (vs >> ρ₂) (injectˡ Δ (lookup (base vl^Var) vˡ))
      ≡⟨ injectˡ->> vs ρ₂ (lookup (base vl^Var) vˡ) ⟩
    lookup vs (lookup (base vl^Var) vˡ)
      ≡⟨ cong (lookup vs) (lookup-base^Var vˡ) ⟩
    lookup vs vˡ
      ≡⟨ lookupᴿ vsᴿ vˡ ⟩
    lookup ws vˡ
      ∎
  ... | inj₂ vʳ = begin
    lookup (vs >> ρ₂) (injectʳ Θ (lookup (base vl^Var) (lookup ρ₁ vʳ)))
      ≡⟨ injectʳ->> vs ρ₂ (lookup (base vl^Var) (lookup ρ₁ vʳ)) ⟩
    lookup ρ₂ (lookup (base vl^Var) (lookup ρ₁ vʳ))
      ≡⟨ cong (lookup ρ₂) (lookup-base^Var (lookup ρ₁ vʳ)) ⟩
    lookup ρ₂ (lookup ρ₁ vʳ)
      ≡⟨ lookupᴿ ρᴿ vʳ ⟩
    lookup ρ₃ vʳ
      ∎
  Fusion.varᴿ  ren-sem = λ ρᴿ v → cong (Semantics.var S) (lookupᴿ ρᴿ v)
  Fusion.algᴿ  ren-sem {Γ} {Δ} {ρ₁} {Θ} {ρ₂} {ρ₃} ρᴿ b zp = begin
    let
      v₁  = fmap d (Ren.body ρ₁) b
      v₃  = fmap d (Semantics.body S ρ₃) b

      aux : fmap d (λ Δ σ → Semantics.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ) v₁
          ≡ fmap d (λ Δ σ → Semantics.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ ∘ Ren.body ρ₁ Δ σ) b
      aux = begin
        fmap d (λ Δ σ → Semantics.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ) v₁
          ≡⟨ fmap² d (Ren.body ρ₁) (λ Δ σ → Semantics.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ) b ⟩
        fmap d (λ Δ σ → Semantics.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ ∘ Ren.body ρ₁ Δ σ) b
          ∎
    in
    Semantics.alg S (fmap d (Semantics.body S ρ₂) (fmap d (reify vl^Var) v₁))
      ≡⟨ cong (Semantics.alg S) (fmap² d (reify vl^Var) (Semantics.body S ρ₂) (fmap d (Ren.body ρ₁) b)) ⟩
    Semantics.alg S (fmap d (λ Δ σ → Semantics.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ) (fmap d (Ren.body ρ₁) b))
      ≡⟨ cong (Semantics.alg S) aux ⟩
    Semantics.alg S (fmap d (λ Δ σ → Semantics.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ ∘ Ren.body ρ₁ Δ σ) b)
      ≡⟨ alg-fusion b ρᴿ (subst (λ t → ⟦ d ⟧ᴿ _ t v₃) aux zp) ⟩
    Semantics.alg S v₃
      ∎
\end{code}

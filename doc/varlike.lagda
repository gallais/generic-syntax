\begin{code}
module varlike where

open import Data.List.Base hiding ([_])
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_])

open import indexed
open import var
open import rel
open import environment

module _ {I : Set} where
\end{code}
%<*varlike>
\begin{code}
 record VarLike (𝓥 : I ─Scoped) : Set where
   field  new   : {i : I} → [ (i ∷_) ⊢ 𝓥 i ]
          th^𝓥  : {i : I} → Thinnable (𝓥 i)
\end{code}
%</varlike>
\begin{code}
   base : ∀ {Γ} → (Γ ─Env) 𝓥 Γ
   base {[]}  = ε
   base {σ ∷ Γ} = th^Env th^𝓥 base extend ∙ new

   freshʳ : (Δ : List I) → ∀ {Γ} → (Γ ─Env) 𝓥 (Δ ++ Γ)
   freshʳ Δ = th^Env th^𝓥 base (pack (injectʳ Δ))

   freshˡ : (Δ : List I) → ∀ {Γ} → (Γ ─Env) 𝓥 (Γ ++ Δ)
   freshˡ k = th^Env th^𝓥 base (pack (injectˡ _))

   singleton : ∀ {Γ σ} → 𝓥 σ Γ → (σ ∷ Γ ─Env) 𝓥 Γ
   singleton v = base ∙ v
 open VarLike public

 vl^Var : VarLike Var
 new   vl^Var = z
 th^𝓥  vl^Var = th^Var

 lookup-base^Var : {Γ : List I} {σ : I} (k : Var σ Γ) → lookup (base vl^Var) k ≡ k
 lookup-base^Var z     = refl
 lookup-base^Var (s k) = cong s (lookup-base^Var k)

module _ {I : Set} {𝓥 : I ─Scoped} (vl^𝓥 : VarLike 𝓥) where

 lift : (Θ : List I) → ∀ {Γ Δ} → (Γ ─Env) 𝓥 Δ → (Θ ++ Γ ─Env) 𝓥 (Θ ++ Δ)
 lift Θ {Γ} {Δ} ρ = freshˡ vl^𝓥 Δ {Θ} >> th^Env (th^𝓥 vl^𝓥) ρ (freshʳ vl^Var Θ)

module _ {I : Set} {𝓥 : I ─Scoped} where
 open ≡-Reasoning

 split-freshʳ : (Δ : List I) {Γ : List I} {i : I} (v : Var i Γ) →
                split Δ (lookup (freshʳ vl^Var Δ) v) ≡ inj₂ v
 split-freshʳ Δ v =
   begin
     split Δ (injectʳ Δ (lookup (base vl^Var) v)) ≡⟨ split-injectʳ Δ (lookup (base vl^Var) v) ⟩
     inj₂ (lookup (base vl^Var) v)                ≡⟨ cong inj₂ (lookup-base^Var v) ⟩
     inj₂ v
   ∎

 freshʳ->> : (Δ : List I) {Γ Θ : List I}
             (ρ₁ : (Δ ─Env) 𝓥 Θ) (ρ₂ : (Γ ─Env) 𝓥 Θ) {i : I} (v : Var i Γ) →
             lookup (ρ₁ >> ρ₂) (lookup (freshʳ vl^Var Δ) v) ≡ lookup ρ₂ v
 freshʳ->> Δ ρ₁ ρ₂ v rewrite split-freshʳ Δ v = refl

module _ {I : Set} {𝓥₁ 𝓥₂ : I ─Scoped} (𝓡^𝓥  : Rel 𝓥₁ 𝓥₂) where

 record VarLike^R (vl₁ : VarLike 𝓥₁) (vl₂ : VarLike 𝓥₂) : Set where
   field  new^R  : {i : I} {Γ : List I} → rel 𝓡^𝓥 {i} {i ∷ Γ} (new vl₁) (new vl₂)
          th^R   : {i : I} {Γ Δ : List I} (σ : Thinning Γ Δ) {v₁ : 𝓥₁ i Γ} {v₂ : 𝓥₂ i Γ} →
                   rel 𝓡^𝓥 v₁ v₂ → rel 𝓡^𝓥 (th^𝓥 vl₁ v₁ σ) (th^𝓥 vl₂ v₂ σ)

   base^R : {Γ : List I} → ∀[ 𝓡^𝓥 ] (base vl₁ {Γ}) (base vl₂)
   base^R {[]   } = pack^R λ ()
   base^R {i ∷ Γ} = (th^R extend <$>^R base^R) ∙^R new^R

   freshˡ^R : (Γ : List I) {Δ : List I} → ∀[ 𝓡^𝓥 ] (freshˡ vl₁ Γ {Δ}) (freshˡ vl₂ Γ)
   freshˡ^R n = th^R _ <$>^R base^R

   freshʳ^R : (Γ : List I) {Δ : List I} → ∀[ 𝓡^𝓥 ] (freshʳ vl₁ Γ {Δ}) (freshʳ vl₂ Γ)
   freshʳ^R n = th^R _ <$>^R base^R


module _ {I : Set} {𝓥 : I ─Scoped} (vl^𝓥  : VarLike 𝓥) where

 vl^Refl : VarLike^R Eq^R vl^𝓥 vl^𝓥
 VarLike^R.new^R  vl^Refl = refl
 VarLike^R.th^R   vl^Refl = λ σ → cong (λ v → th^𝓥 vl^𝓥 v σ)

module _ {I : Set} {𝓥₁ 𝓥₂ 𝓒₁ 𝓒₂ : I ─Scoped} (𝓡^𝓥  : Rel 𝓥₁ 𝓥₂) (𝓡^𝓒  : Rel 𝓒₁ 𝓒₂) where

\end{code}
%<*kripkeR>
\begin{code}
 Kripke^R : (Δ : List I) (τ : I) → [ Kripke 𝓥₁ 𝓒₁ Δ τ ⟶ Kripke 𝓥₂ 𝓒₂ Δ τ ⟶ κ Set ]
 Kripke^R []       σ k₁ k₂ = rel 𝓡^𝓒 k₁ k₂
 Kripke^R (τ ∷ Δ)  σ k₁ k₂ = {Θ : List I} → ∀ th {ρ₁} {ρ₂} → ∀[ 𝓡^𝓥 ] ρ₁ ρ₂ → rel 𝓡^𝓒 {σ} {Θ} (k₁ th ρ₁) (k₂ th ρ₂)
\end{code}
%</kripkeR>

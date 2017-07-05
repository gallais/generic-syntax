\begin{code}
module Generic.Fusion where

open import Size
open import Data.List hiding ([_] ; zip)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import indexed
open import rel
open import var hiding (_<$>_)
open import varlike
open import environment hiding (refl)

open import Generic.Syntax
open import Generic.Semantics
open import Generic.Zip

module _  {I : Set} {𝓥₁ 𝓥₂ 𝓥₃ 𝓒₁ 𝓒₂ 𝓒₃ : I → List I → Set}
          (𝓡^Env : {Γ Δ Θ : List I} → (Γ ─Env) 𝓥₁ Δ → (Δ ─Env) 𝓥₂ Θ → (Γ ─Env) 𝓥₃ Θ → Set)
          (𝓡^𝓥  : Rel 𝓥₂ 𝓥₃)
          (𝓡^𝓒   : Rel 𝓒₂ 𝓒₃)
          where

 record Fus (d : Desc I) (𝓢₁ : Sem d 𝓥₁ 𝓒₁) (𝓢₂ : Sem d 𝓥₂ 𝓒₂) (𝓢₃ : Sem d 𝓥₃ 𝓒₃) : Set where
   field  quote₁  : (i : I) → [ 𝓒₁ i ⟶ Tm d ∞ i ]
          vl^𝓥₁  : VarLike 𝓥₁
          var^R   : {Γ Δ Θ : List I} {i : I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} →
                    𝓡^Env ρ₁ ρ₂ ρ₃ → (v : Var i Γ) →
                    rel 𝓡^𝓒 (Sem.sem 𝓢₂ ρ₂ (quote₁ i (Sem.var 𝓢₁ (lookup ρ₁ v)))) (Sem.var 𝓢₃ (lookup ρ₃ v))
          alg^R   : {Γ Δ : List I} {i : I} {b₁ : ⟦ d ⟧ (Kripke 𝓥₁ 𝓒₁) i Γ} {b₃ : ⟦ d ⟧ (Kripke 𝓥₃ 𝓒₃) i Δ} →
                    {ρ₂ : (Γ ─Env) 𝓥₂ Δ} →
                    Zip d (Kripke^R 𝓡^𝓥 𝓡^𝓒) (fmap d (λ Δ i → Sem.body 𝓢₂ ρ₂ Δ i ∘ quote₁ i ∘ reify vl^𝓥₁ Δ i) b₁) b₃ →
                    rel 𝓡^𝓒 (Sem.sem 𝓢₂ ρ₂ (quote₁ i (Sem.alg 𝓢₁ b₁))) (Sem.alg 𝓢₃ b₃)


   fus  : {s : Size} {i : I} {Γ Δ Θ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} →
          𝓡^Env ρ₁ ρ₂ ρ₃ → (t : Tm d s i Γ) →
          rel 𝓡^𝓒  (Sem.sem 𝓢₂ ρ₂ (quote₁ i (Sem.sem 𝓢₁ ρ₁ t)))
                     (Sem.sem 𝓢₃ ρ₃ t)
   body : {s : Size} {Γ Θ Ξ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Θ} {ρ₂ : (Θ ─Env) 𝓥₂ Ξ} {ρ₃ : (Γ ─Env) 𝓥₃ Ξ} →
          𝓡^Env ρ₁ ρ₂ ρ₃ → (Δ : List I) (i : I) (b : Scope (Tm d s) Δ i Γ) →
          Kripke^R 𝓡^𝓥 𝓡^𝓒 Δ i (Sem.body 𝓢₂ ρ₂ Δ i (quote₁ i (reify vl^𝓥₁ Δ i (Sem.body 𝓢₁ ρ₁ Δ i b))))
                                   (Sem.body 𝓢₃ ρ₃ Δ i b)

   fus ρ^R (`var v) = var^R ρ^R v
   fus ρ^R (`con t) = alg^R (rew (zip d (body ρ^R) t)) where

     eq  = fmap² d (Sem.body 𝓢₁ _) (λ Δ i t → Sem.body 𝓢₂ _ Δ i (quote₁ i (reify vl^𝓥₁ Δ i t))) t
     rew = subst (λ v → Zip d (Kripke^R 𝓡^𝓥 𝓡^𝓒) v _) (sym eq)

   body ρ^R []       i b = fus ρ^R b
   body ρ^R (σ ∷ Δ)  i b = λ ren vs^R → {!!}


module _ {I : Set} (d : Desc I) where

 Ren² : Fus (λ ρ₁ → ∀[ Eq^R ] ∘ (select ρ₁)) Eq^R Eq^R d Renaming Renaming Renaming
 Fus.quote₁ Ren² = λ _ t → t
 Fus.vl^𝓥₁ Ren² = vl^Var
 Fus.var^R  Ren² = λ ρ^R v → cong `var (lookup^R ρ^R v)
 Fus.alg^R  Ren² = λ z → cong `con {!!}

 ren² : ∀ {Γ Δ Θ i} (t : Tm d ∞ i Γ) (ρ₁ : Thinning Γ Δ) (ρ₂ : Thinning Δ Θ) →
        ren ρ₂ (ren ρ₁ t) ≡ ren (select ρ₁ ρ₂) t
 ren² t ρ₁ ρ₂ = Fus.fus Ren² (pack^R (λ _ → refl)) t
\end{code}

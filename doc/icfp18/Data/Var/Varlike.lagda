\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Data.Var.Varlike where

open import Data.List.Base hiding (lookup ; [_])
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Relation.Unary using (IUniversal; _⊢_; _⇒_)
open import Data.Var
open import Data.Pred as Pred hiding (All)
open import Data.Relation
open import Data.Environment
open import Generic.Syntax

private
  variable
    I : Set
    σ : I
    Γ Δ : List I
    𝓥 𝓥₁ 𝓥₂ 𝓒 𝓥ᴬ 𝓥ᴮ 𝓒ᴬ 𝓒ᴮ : I ─Scoped

\end{code}
%<*varlike>
\begin{code}
record VarLike (𝓥 : I ─Scoped) : Set where
  field  th^𝓥  : Thinnable (𝓥 σ)
         new   : ∀[ (σ ∷_) ⊢ 𝓥 σ ]
\end{code}
%</varlike>
\begin{code}

  base : (Γ ─Env) 𝓥 Γ
  base {Γ = []}    = ε
  base {Γ = σ ∷ Γ} = th^Env th^𝓥 base extend ∙ new

  freshʳ : (Δ : List I) → (Γ ─Env) 𝓥 (Δ ++ Γ)
  freshʳ Δ = th^Env th^𝓥 base (pack (injectʳ Δ))

  freshˡ : (Δ : List I) → (Γ ─Env) 𝓥 (Γ ++ Δ)
  freshˡ k = th^Env th^𝓥 base (pack (injectˡ _))

  singleton : 𝓥 σ Γ → (σ ∷ Γ ─Env) 𝓥 Γ
  singleton v = base ∙ v
open VarLike public

vl^Var : VarLike {I} Var
new   vl^Var = z
th^𝓥  vl^Var = th^Var

lookup-base^Var : (k : Var σ Γ) → lookup (base vl^Var) k ≡ k
lookup-base^Var z     = refl
lookup-base^Var (s k) = cong s (lookup-base^Var k)

\end{code}
%<*reify>
\begin{code}
reify : VarLike 𝓥 → ∀ Δ i → Kripke 𝓥 𝓒 Δ i Γ → Scope 𝓒 Δ i Γ
reify vl^𝓥 []         i b = b
reify vl^𝓥 Δ@(_ ∷ _)  i b = b (freshʳ vl^Var Δ) (freshˡ vl^𝓥 _)
\end{code}
%</reify>
\begin{code}
module _ (vl^𝓥 : VarLike 𝓥) where

  lift : ∀ Θ → (Γ ─Env) 𝓥 Δ → ((Θ ++ Γ) ─Env) 𝓥 (Θ ++ Δ)
  lift Θ ρ = freshˡ vl^𝓥 _ >> th^Env (th^𝓥 vl^𝓥) ρ (freshʳ vl^Var Θ)

  extend-is-fresh : All Eqᴿ Γ extend (freshʳ vl^Var (σ ∷ []))
  lookupᴿ extend-is-fresh k = cong s (sym (lookup-base^Var k))

module _ {I : Set} {𝓥 : I ─Scoped} where
 open ≡-Reasoning

 freshʳ->> : (Δ : List I) {Γ Θ : List I}
             (ρ₁ : (Δ ─Env) 𝓥 Θ) (ρ₂ : (Γ ─Env) 𝓥 Θ) {i : I} (v : Var i Γ) →
             lookup (ρ₁ >> ρ₂) (lookup (freshʳ vl^Var Δ) v) ≡ lookup ρ₂ v
 freshʳ->> Δ ρ₁ ρ₂ v = begin
   lookup (ρ₁ >> ρ₂) (lookup (freshʳ vl^Var Δ) v)
     ≡⟨ injectʳ->> ρ₁ ρ₂ (lookup (base vl^Var) v) ⟩
   lookup ρ₂ (lookup (base vl^Var) v)
     ≡⟨ cong (lookup ρ₂) (lookup-base^Var v) ⟩
   lookup ρ₂ v
     ∎

module _ (𝓡^𝓥  : Rel 𝓥₁ 𝓥₂) where

 record VarLikeᴿ (vl₁ : VarLike 𝓥₁) (vl₂ : VarLike 𝓥₂) : Set where
   field  newᴿ  : rel 𝓡^𝓥 σ {σ ∷ Γ} (new vl₁) (new vl₂)
          thᴿ   : (ρ : Thinning Γ Δ) {v₁ : 𝓥₁ σ Γ} {v₂ : 𝓥₂ σ Γ} →
                   rel 𝓡^𝓥 σ v₁ v₂ → rel 𝓡^𝓥 σ (th^𝓥 vl₁ v₁ ρ) (th^𝓥 vl₂ v₂ ρ)

   baseᴿ : All 𝓡^𝓥 Γ (base vl₁) (base vl₂)
   baseᴿ {[]   } = packᴿ λ ()
   baseᴿ {i ∷ Γ} = (thᴿ extend <$>ᴿ baseᴿ) ∙ᴿ newᴿ

   freshˡᴿ : ∀ Γ → All 𝓡^𝓥 Δ (freshˡ vl₁ Γ) (freshˡ vl₂ Γ)
   freshˡᴿ n = thᴿ _ <$>ᴿ baseᴿ

   freshʳᴿ : ∀ Γ → All 𝓡^𝓥 Δ (freshʳ vl₁ Γ) (freshʳ vl₂ Γ)
   freshʳᴿ n = thᴿ _ <$>ᴿ baseᴿ


module _ (vl^𝓥  : VarLike 𝓥) where

 vl^Refl : VarLikeᴿ Eqᴿ vl^𝓥 vl^𝓥
 VarLikeᴿ.newᴿ  vl^Refl = refl
 VarLikeᴿ.thᴿ   vl^Refl = λ σ → cong (λ v → th^𝓥 vl^𝓥 v σ)


module _ (𝓥ᴾ : Pred {I} 𝓥) (𝓒ᴾ : Pred {I} 𝓒) where

 Kripkeᴾ : ∀ Δ τ → ∀[ Kripke 𝓥 𝓒 Δ τ ⇒ const Set ]
 Kripkeᴾ []         τ k = pred 𝓒ᴾ τ k
 Kripkeᴾ Δ@(_ ∷ _)  τ k = ∀ {Θ} th {ρ : (Δ ─Env) 𝓥 Θ} → Pred.All 𝓥ᴾ Δ ρ → pred 𝓒ᴾ τ (k th ρ)

module _ (𝓥ᴿ : Rel {I} 𝓥ᴬ 𝓥ᴮ) (𝓒ᴿ : Rel {I} 𝓒ᴬ 𝓒ᴮ) where
\end{code}
%<*kripkeR>
\begin{code}
 Kripkeᴿ : ∀ Δ i → ∀[ Kripke 𝓥ᴬ 𝓒ᴬ Δ i ⇒ Kripke 𝓥ᴮ 𝓒ᴮ Δ i ⇒ const Set ]
 Kripkeᴿ []         σ kᴬ kᴮ = rel 𝓒ᴿ σ kᴬ kᴮ
 Kripkeᴿ Δ@(_ ∷ _)  σ kᴬ kᴮ = ∀ {Θ} (ρ : Thinning _ Θ) {vsᴬ vsᴮ} →
                              All 𝓥ᴿ Δ vsᴬ vsᴮ → rel 𝓒ᴿ σ (kᴬ ρ vsᴬ) (kᴮ ρ vsᴮ)
\end{code}
%</kripkeR>

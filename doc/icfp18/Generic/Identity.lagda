\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Identity where

open import Size
open import Agda.Builtin.List
open import Data.Product hiding (zip)
open import Data.Sum
open import Data.Var
open import Data.Relation as R
open import Data.Var.Varlike
open import Data.Environment
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Relator
open import Generic.Simulation
open import Generic.Simulation.Syntactic

open import Function
open import Relation.Binary.PropositionalEquality as PEq
open import Relation.Binary.PropositionalEquality.WithK
open ≡-Reasoning

private
  variable
    I : Set
    d : Desc I
    σ : I
    Γ : List I
    i j : Size

data _≅_ {d : Desc I} {σ} {Γ} : {s : Size} → Tm d s σ Γ → {t : Size} → Tm d t σ Γ → Set
⟨_⟩_≅_ : {d : Desc I} (e : Desc I) → ⟦ e ⟧ (Scope (Tm d i)) σ Γ → ⟦ e ⟧ (Scope (Tm d j)) σ Γ → Set

data _≅_ {d = d} {σ} {Γ} where
  `var : {k l : Var σ Γ} → k ≡ l → `var {s = i} k ≅ `var {s = j} l
  `con : {b : ⟦ d ⟧ (Scope (Tm d i)) σ Γ} {c : ⟦ d ⟧ (Scope (Tm d j)) σ Γ} →
         ⟨ d ⟩ b ≅ c → `con {s = i} b ≅ `con {s = j} c

⟨ e ⟩ b ≅ c = ⟦ e ⟧ᴿ (λ _ _  t u → t ≅ u) b c

≅⇒≡    : ∀ {t u : Tm d ∞ σ Γ} → t ≅ u → t ≡ u
⟨_⟩≅⇒≡ : ∀ e {t u : ⟦ e ⟧ (Scope (Tm d ∞)) σ Γ} → ⟨ e ⟩ t ≅ u → t ≡ u

≅⇒≡ (`var eq) = cong `var eq
≅⇒≡ (`con eq) = cong `con (⟨ _ ⟩≅⇒≡ eq)

⟨ `σ A d   ⟩≅⇒≡ (refl , eq) = cong -,_ (⟨ d _ ⟩≅⇒≡ eq)
⟨ `X Δ j d ⟩≅⇒≡ (≅-pr , eq) = cong₂ _,_ (≅⇒≡ ≅-pr) (⟨ d ⟩≅⇒≡ eq)
⟨ `∎ i     ⟩≅⇒≡ eq          = ≡-irrelevant _ _

module RenId {I : Set} {d : Desc I} where

 ren-id      : ∀ (t : Tm d i σ Γ) {ρ} → R.All Eqᴿ Γ ρ (base vl^Var) → ren ρ t ≅ t
 ren-body-id : ∀ Δ σ (t : Scope (Tm d i) Δ σ Γ) {ρ} → R.All Eqᴿ Γ ρ (base vl^Var) →
               reify vl^Var Δ σ (Semantics.body Ren ρ Δ σ t) ≅ t

 ren-id (`var k) ρᴿ = `var (trans (lookupᴿ ρᴿ k) (lookup-base^Var k))
 ren-id (`con t) ρᴿ = `con (subst₂ (⟨ d ⟩_≅_) (sym $ fmap² d (Semantics.body Ren _) (reify vl^Var) _) (fmap-id d _)
                            $ liftᴿ d (λ Δ i t → ren-body-id Δ i t ρᴿ) _)

 ren-body-id []        σ t    = ren-id t
 ren-body-id {Γ = Γ} Δ@(_ ∷ _) σ t {ρ} ρᴿ = ren-id t eqᴿ where

  eqᴿ : R.All Eqᴿ _ (lift vl^Var Δ ρ) (base vl^Var)
  lookupᴿ eqᴿ k with split Δ k | inspect (split Δ) k
  ... | inj₁ k₁ | PEq.[ eq ] = begin
    injectˡ Γ (lookup (base vl^Var) k₁) ≡⟨ cong (injectˡ Γ) (lookup-base^Var k₁) ⟩
    injectˡ Γ k₁                        ≡⟨ sym (lookup-base^Var k) ⟩
    lookup (base vl^Var) k              ∎
  ... | inj₂ k₂ | PEq.[ eq ] = begin
    injectʳ Δ (lookup (base vl^Var) (lookup ρ k₂)) ≡⟨ cong (injectʳ Δ) (lookup-base^Var _) ⟩
    injectʳ Δ (lookup ρ k₂)                        ≡⟨ cong (injectʳ Δ) (lookupᴿ ρᴿ k₂) ⟩
    injectʳ Δ (lookup (base vl^Var) k₂)            ≡⟨ cong (injectʳ Δ) (lookup-base^Var k₂) ⟩
    k                                              ≡⟨ sym (lookup-base^Var k) ⟩
    lookup (base vl^Var) k                         ∎

module _ {I : Set} {d : Desc I} where

  ren-id : ∀ {σ Γ} (t : Tm d ∞ σ Γ) → ren (base vl^Var) t ≡ t
  ren-id t = ≅⇒≡ (RenId.ren-id t (packᴿ λ _ → refl))

  ren-id′ : ∀ {σ Γ} (t : Tm d ∞ σ Γ) → ren (pack id) t ≡ t
  ren-id′ t = ≅⇒≡ (RenId.ren-id t (packᴿ λ v → sym (lookup-base^Var v)))

  sub-id : ∀ {σ Γ} (t : Tm d ∞ σ Γ) → sub (base vl^Tm) t ≡ t
  sub-id t = begin
    sub (base vl^Tm) t  ≡⟨ sym $ Simulation.sim RenSub base^VarTmᴿ t ⟩
    ren (base vl^Var) t ≡⟨ ren-id t ⟩
    t                   ∎

  sub-id′ : ∀ {σ Γ} (t : Tm d ∞ σ Γ) → sub (pack `var) t ≡ t
  sub-id′ t = begin
    sub (pack `var) t ≡⟨ sym $ Simulation.sim RenSub (packᴿ λ v → refl) t ⟩
    ren (pack id)   t ≡⟨ ren-id′ t ⟩
    t                 ∎

  lift[]^Tm : ∀ {Γ Δ} (ρ : (Γ ─Env) (Tm d ∞) Δ) → R.All Eqᴿ Γ ρ (lift vl^Tm [] ρ)
  lookupᴿ (lift[]^Tm ρ) k = sym (ren-id (lookup ρ k))


  th^base₁^Var : ∀ {Γ Δ} (ρ : Thinning {I} Γ Δ) → R.All Eqᴿ Γ (th^Env th^Var (base vl^Var) ρ) ρ
  lookupᴿ (th^base₁^Var ρ) k = cong (lookup ρ) (lookup-base^Var k)

  th^base₂^Var : ∀ {Γ Δ} (ρ : Thinning {I} Γ Δ) → R.All Eqᴿ Γ (th^Env th^Var ρ (base vl^Var)) ρ
  lookupᴿ (th^base₂^Var ρ) k = `var-inj (ren-id (`var (lookup ρ k)))

  th^base^Tm : ∀ {Γ Δ} (ρ : (Γ ─Env) (Tm d ∞) Δ) → R.All Eqᴿ Γ (th^Env th^Tm ρ (base vl^Var)) ρ
  lookupᴿ (th^base^Tm ρ) k = ren-id (lookup ρ k)

  th^base^s∙z : ∀ {σ Γ} → R.All Eqᴿ _ (th^Env th^Tm (base vl^Tm) (pack s) ∙ `var z)
                                      ((σ ∷ Γ ─Env) (Tm d ∞) (σ ∷ Γ) ∋ pack `var)
  lookupᴿ th^base^s∙z z     = refl
  lookupᴿ th^base^s∙z (s k) = cong (ren (pack s)) (lookup-base^Tm k)
\end{code}

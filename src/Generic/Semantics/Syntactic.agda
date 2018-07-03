module Generic.Semantics.Syntactic where

open import Size
open import Data.List hiding ([_] ; lookup)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import indexed
open import var
open import varlike
open import environment
open import rel
open import Generic.Syntax
open import Generic.Semantics

module _ {I : Set} {d : Desc I} where

 Renaming : Sem d Var (Tm d ∞)
 Sem.th^𝓥  Renaming = λ k ρ → lookup ρ k
 Sem.var   Renaming = `var
 Sem.alg   Renaming = `con ∘ fmap d (reify vl^Var)

 ren :  {Γ Δ : List I} → (Γ ─Env) Var Δ →
        (Γ ─Comp) (Tm d ∞) Δ
 ren = Sem.sem Renaming

 th^Tm : {i : I} → Thinnable (Tm d ∞ i)
 th^Tm t ρ = Sem.sem Renaming ρ t

 vl^Tm : VarLike (Tm d ∞)
 new   vl^Tm = `var z
 th^𝓥  vl^Tm = th^Tm

 Substitution : Sem d (Tm d ∞) (Tm d ∞)
 Sem.th^𝓥  Substitution = λ t ρ → ren ρ t
 Sem.var   Substitution = id
 Sem.alg   Substitution = `con ∘ fmap d (reify vl^Tm)

 sub :  {Γ Δ : List I} → (Γ ─Env) (Tm d ∞) Δ →
        (Γ ─Comp) (Tm d ∞) Δ
 sub = Sem.sem Substitution

 vl^VarTm : VarLike^R VarTm^R vl^Var vl^Tm
 VarLike^R.new^R  vl^VarTm = refl
 VarLike^R.th^R   vl^VarTm = λ σ → cong (ren σ)

 reify^Tm : ∀ Δ {σ} → [ Kripke (Tm d ∞) (Tm d ∞) Δ σ ⟶ (Δ ++_) ⊢ Tm d ∞ σ ]
 reify^Tm Δ = reify vl^Tm Δ _

 lookup-base^Tm : {Γ : List I} {σ : I} (k : Var σ Γ) → lookup (base vl^Tm) k ≡ `var k
 lookup-base^Tm z                              = refl
 lookup-base^Tm (s k) rewrite lookup-base^Tm k = refl

 base^VarTm^R : ∀ {Γ} → ∀[ VarTm^R ] (base vl^Var {Γ}) (base vl^Tm)
 lookup^R base^VarTm^R k = begin
   `var (lookup (base vl^Var) k) ≡⟨ cong `var (lookup-base^Var k) ⟩
   `var k                        ≡⟨ sym (lookup-base^Tm k) ⟩
   lookup (base vl^Tm) k ∎

 infix 5 _[_
 infix 6 _/0]

 _/0] : ∀ {σ Γ} → Tm d ∞ σ Γ → (σ ∷ Γ ─Env) (Tm d ∞) Γ
 _/0] = singleton vl^Tm

 _[_ : ∀ {σ τ Γ} → Tm d ∞ τ (σ ∷ Γ) → (σ ∷ Γ ─Env) (Tm d ∞) Γ → Tm d ∞ τ Γ
 t [ ρ = sub ρ t


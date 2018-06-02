\begin{code}
module rel where

open import Size
open import Data.Sum
open import Data.List.Base hiding ([_]; lookup)

open import indexed
open import var hiding (_<$>_)
open import environment
open import Generic.Syntax
open import Agda.Builtin.Equality

record Rel {I : Set} (T U : I ─Scoped) : Set₁ where
  constructor mkRel
  field rel : {i : I} → [ T i ⟶ U i ⟶ κ Set ]
open Rel public

module _ {I : Set} {T U : I ─Scoped} where

 record ∀[_] (𝓡 : Rel T U) {Γ Δ : List I}
             (ρ₁ : (Γ ─Env) T Δ) (ρ₂ : (Γ ─Env) U Δ) : Set where
   constructor pack^R
   field lookup^R : ∀ {i} k → rel 𝓡 {i} (lookup ρ₁ k) (lookup ρ₂ k)
 open ∀[_] public

module _ {I : Set} {T U : I ─Scoped}
         {𝓡 : Rel T U} {Δ : List I} where

 ε^R : {ρ₁ : ([] ─Env) T Δ} {ρ₂ : ([] ─Env) U Δ} → ∀[ 𝓡 ] ρ₁ ρ₂
 lookup^R ε^R ()

module _ {I : Set} {T U : I ─Scoped}
         {𝓡 : Rel T U} {Γ Δ : List I} where

 infixl 20 _∙^R_
 _∙^R_ :  {ρ₁ : (Γ ─Env) T Δ} {ρ₂ : (Γ ─Env) U Δ} → ∀[ 𝓡 ] ρ₁ ρ₂ →
          {i : I} {v₁ : T i Δ} {v₂ : U i Δ} → rel 𝓡 v₁ v₂ →
          ∀[ 𝓡 ] (ρ₁ ∙ v₁) (ρ₂ ∙ v₂)
 lookup^R (ρ ∙^R v) z      = v
 lookup^R (ρ ∙^R v) (s k)  = lookup^R ρ k

 _>>^R_ :  {Γ′ : List I}
           {ρ₁  : (Γ  ─Env) T Δ} {ρ₂  : (Γ  ─Env) U Δ} → ∀[ 𝓡 ] ρ₁ ρ₂ →
           {ρ₁′ : (Γ′ ─Env) T Δ} {ρ₂′ : (Γ′ ─Env) U Δ} → ∀[ 𝓡 ] ρ₁′ ρ₂′ →
           ∀[ 𝓡 ] (ρ₁ >> ρ₁′) (ρ₂ >> ρ₂′)
 lookup^R (_>>^R_ ρ^R ρ′^R) k with split Γ k
 ... | inj₁ k₁ = lookup^R ρ^R k₁
 ... | inj₂ k₂ = lookup^R ρ′^R k₂

 _<$>^R_ : {Θ : List I} {f : {i : I} → T i Δ → T i Θ} {g : {i : I} → U i Δ → U i Θ} →
           ({i : I} {t : T i Δ} {u : U i Δ} → rel 𝓡 t u → rel 𝓡 (f t) (g u)) →
           {ρ₁ : (Γ ─Env) T Δ} {ρ₂ : (Γ ─Env) U Δ} →
           ∀[ 𝓡 ] ρ₁ ρ₂ → ∀[ 𝓡 ] (f <$> ρ₁) (g <$> ρ₂)
 lookup^R (F <$>^R ρ) k = F (lookup^R ρ k)

module _ {I : Set} where

 Eq^R : {A : I ─Scoped} → Rel A A
 rel Eq^R = _≡_

 open import Relation.Binary.HeterogeneousEquality.Core

 HEq^R : {A B : I ─Scoped} → Rel A B
 rel HEq^R = λ a b → a ≅ b

module _ {I : Set} {d : Desc I} where

 VarTm^R : Rel Var (Tm d ∞)
 rel VarTm^R v t = `var v ≡ t

\end{code}


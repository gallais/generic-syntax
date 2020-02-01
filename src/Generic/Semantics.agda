{-# OPTIONS --safe --sized-types #-}

module Generic.Semantics where

open import Size
open import Data.List.Base as L hiding (lookup ; [_])

open import Data.Var hiding (z; s)
open import Data.Var.Varlike using (VarLike; base)
open import Data.Relation
open import Relation.Unary
open import Data.Environment
open import Function using (flip)
open import Generic.Syntax

private
  variable
    I : Set
    σ : I
    Γ Δ : List I
    s : Size
    d : Desc I

module _  {d : Desc I} where


  _─Comp : List I → I ─Scoped → List I → Set
  (Γ ─Comp) 𝓒 Δ = ∀ {s σ} → Tm d s σ Γ → 𝓒 σ Δ

  private
   module DISPLAYONLY where

   record Semantics (d : Desc I) (𝓥 𝓒 : I ─Scoped) : Set where
     field th^𝓥  : Thinnable (𝓥 σ)
           var   : ∀[ 𝓥 σ ⇒ 𝓒 σ ]
           alg   : ∀[ ⟦ d ⟧ (Kripke 𝓥 𝓒) σ ⇒ 𝓒 σ ]

record Semantics (d : Desc I) (𝓥 𝓒 : I ─Scoped) : Set where

 field

   th^𝓥 : Thinnable (𝓥 σ)

   var : ∀[ 𝓥 σ ⇒ 𝓒 σ ]

   alg : ∀[ ⟦ d ⟧ (Kripke 𝓥 𝓒) σ ⇒ 𝓒 σ ]

 semantics : (Γ ─Env) 𝓥 Δ → (Γ ─Comp) 𝓒 Δ
 body      : (Γ ─Env) 𝓥 Δ → ∀ Θ σ →
             Scope (Tm d s) Θ σ Γ → Kripke 𝓥 𝓒 Θ σ Δ

 semantics ρ (`var k) = var (lookup ρ k)
 semantics ρ (`con t) = alg (fmap d (body ρ) t)

 body ρ []       i t = semantics ρ t
 body ρ (_ ∷ _)  i t = λ σ vs → semantics (vs >> th^Env th^𝓥 ρ σ) t

 ◇-sem  : (Γ ─◇Env) 𝓥 Δ → (Γ ─Comp) 𝓒 Δ
 ◇-body : (Γ ─◇Env) 𝓥 Δ → ∀ Θ σ →
          Scope (Tm d s) Θ σ Γ → Kripke 𝓥 𝓒 Θ σ Δ

 ◇-sem ρ (`var k) = var (DI.run th^𝓥 (slookup ρ k))
 ◇-sem ρ (`con t) = alg (fmap d (◇-body ρ) t)

 ◇-body ρ []        i t = ◇-sem ρ t
 ◇-body ρ Δ@(_ ∷ _) i t = λ σ vs → ◇-sem (Δ ⊣ vs ,, ρ ◃ σ) t

 closed : TM d σ → 𝓒 σ []
 closed = semantics ε

 eval : VarLike 𝓥 → ∀[ Tm d s σ ⇒ 𝓒 σ ]
 eval vl^𝓥 = semantics (base vl^𝓥)

module Generic.Closure where

open import Size
open import Data.List.Base as L using (List; []; _∷_)
open import Function

open import Data.Var hiding (z; s; _<$>_)
open import Relation.Unary
open import Data.Environment as E hiding (sequenceA)

open import Generic.Syntax
open import Generic.Semantics

private
  variable
    I : Set
    i σ : I
    Γ₁ Γ₂ : List I
    Γ Δ  : List I
    s : Size
    X Y : List I → I ─Scoped

data Tm' (d : Desc I) : Size → I ─Scoped where
  `var  : ∀[ Var i                      ⇒ Tm' d (↑ s) i ]
  `cls  : (Γ ─Env) (Tm' d s) Δ → Tm' d s i Γ →  Tm' d (↑ s) i Δ
  `con  : ∀[ ⟦ d ⟧ (Scope (Tm' d s)) i  ⇒ Tm' d (↑ s) i ]


module _ {I} {d : Desc I} {𝓥 𝓒} (𝓢 : Semantics d 𝓥 𝓒) where

 open Semantics 𝓢

 sem'  : □ ((Γ ─Env) 𝓒) Δ → ∀ {s σ} → Tm' d s σ Γ → 𝓒 σ Δ
 body' : □ ((Γ ─Env) 𝓒) Δ → ∀ Θ σ → Scope (Tm' d s) Θ σ Γ → Kripke 𝓥 𝓒 Θ σ Δ

 sem' σ (`var k)           = lookup (extract σ) k
 sem' σ (`con t)           = alg (fmap d (body' σ) t)
 sem' σ (`cls {Γ = Γ} ρ t) = sem' σ' t where
   σ' : □ ((Γ ─Env) 𝓒) _
   σ' θ = sem' (λ θ' → σ (select θ θ')) <$> ρ

 body' σ []       i t = sem' σ t
 body' σ (_ ∷ _)  i t = λ θ vs → sem' (λ ρ → ((var ∘ (λ v → th^𝓥 v ρ)) <$> vs) >> σ (select θ ρ)) t


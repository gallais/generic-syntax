module Generic.Semantics where

open import Size
open import Data.List.Base as L hiding (lookup ; [_])

open import var
open import rel
open import indexed
open import environment as E
open import Generic.Syntax

module _ {I : Set} where

 Alg : (d : Desc I) (𝓥 𝓒 : I ─Scoped) → Set
 Alg d 𝓥 𝓒 = {i : I} → [ ⟦ d ⟧ (Kripke 𝓥 𝓒) i ⟶ 𝓒 i ]

module _ {I : Set} {d : Desc I} where

 _─Comp : List I → I ─Scoped → List I → Set
 (Γ ─Comp) 𝓒 Δ = {s : Size} {i : I} → Tm d s i Γ → 𝓒 i Δ

record Sem {I : Set} (d : Desc I) (𝓥 𝓒 : I ─Scoped) : Set where
 field  th^𝓥   : {i : I} → Thinnable (𝓥 i)
        var    : {i : I} → [ 𝓥 i                   ⟶ 𝓒 i ]
        alg    : {i : I} → [ ⟦ d ⟧ (Kripke 𝓥 𝓒) i  ⟶ 𝓒 i ]

 sem   :  {Γ Δ : List I} → (Γ ─Env) 𝓥 Δ → (Γ ─Comp) 𝓒 Δ
 body  :  {Γ Δ : List I} {s : Size} → (Γ ─Env) 𝓥 Δ → ∀ Θ i → Scope (Tm d s) Θ i Γ → Kripke 𝓥 𝓒 Θ i Δ

 sem ρ (`var k) = var (lookup ρ k)
 sem ρ (`con t) = alg (fmap d (body ρ) t)

 body ρ []       i t = sem ρ t
 body ρ (_ ∷ _)  i t = λ σ vs → sem (vs >> th^Env th^𝓥 ρ σ) t

 closed : ([] ─Comp) 𝓒 []
 closed = sem ε

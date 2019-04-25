{-# OPTIONS --safe --sized-types #-}

--------------------------------------------------------------------------------
-- This module replicates (a generic version of) the result proven in
-- Binder Aware Recursion over Well-scoped De Bruijn Syntax
-- (Kaiser, Schäfer, and Stark, CPP 2018)
--
-- In it they claim that assuming functional extensionality it is possible to
-- prove that all of the Semantics in the sense of
-- Type-and-scope Safe Programs and Their Proofs
-- (Allais, Chapman, McBride, and McKinna, CPP 2017)
-- are renaming-compatible.
--
-- In practice we however refrain from using this module whenever we can obtain
-- an axiom-free version of the result (cf. Generic.Fusion.Syntactic for instance).
--------------------------------------------------------------------------------

module Generic.Fusion.Specialised.Replication where

open import Data.Var
open import Data.Environment
open import Data.Var.Varlike
open import Data.Relation
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Relator
open import Generic.Fusion
import Generic.Fusion.Specialised.Propositional as FusProp
open import Generic.Identity

open import Size
open import Function
open import Data.Sum
open import Data.Product
open import Data.List.Base hiding (lookup)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning


module _
  (fun-ext : ∀ {ℓ ℓ′} {A : Set ℓ} {B : A → Set ℓ′} {f g : (a : A) → B a} →
             (∀ x → f x ≡ g x) → f ≡ g)
  (ifun-ext : ∀ {ℓ ℓ′} {A : Set ℓ} {B : A → Set ℓ′} {f g : {a : A} → B a} →
              (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ g)
  {I} (d : Desc I) {𝓥 𝓒} (S : Semantics d 𝓥 𝓒) where

  alg-fusion : ∀ {i σ Γ Δ Θ} (b : ⟦ d ⟧ (Scope (Tm d i)) σ Γ) {ρ₁ ρ₃} {ρ₂ : (Δ ─Env) 𝓥 Θ} →
    All Eqᴿ _ (select ρ₁ ρ₂) ρ₃ →
    let f = λ Δ σ → Semantics.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ ∘ Semantics.body Ren ρ₁ Δ σ
        g = Semantics.body S ρ₃
    in ⟦ d ⟧ᴿ (Kripkeᴿ Eqᴿ Eqᴿ) (fmap d f b) (fmap d g b) →
    Semantics.alg S (fmap d f b) ≡ Semantics.alg S (fmap d g b)
  alg-fusion {i} {σ} {Γ} {Δ} {Θ} b {ρ₁} {ρ₃} {ρ₂} ρᴿ zp = begin
    Semantics.alg S (fmap d f b)
      ≡⟨ cong (Semantics.alg S) (zip-eq d b zp) ⟩
    Semantics.alg S (fmap d g b)
      ∎ where

    ren₁  = Semantics.body Ren ρ₁
    eval₂ = Semantics.body S ρ₂
    f     = λ Δ σ → eval₂ Δ σ ∘ reify vl^Var Δ σ ∘ ren₁ Δ σ
    g     = λ Δ σ → Semantics.body S ρ₃ Δ σ


    kripke-eq : ∀ Δ σ (t : Scope (Tm d i) Δ σ Γ) → Kripkeᴿ Eqᴿ Eqᴿ Δ σ (f Δ σ t) (g Δ σ t) → f Δ σ t ≡ g Δ σ t
    kripke-eq []        j x kr = kr
    kripke-eq Δ@(_ ∷ _) j x kr = ifun-ext $ λ Γ → fun-ext $ λ r → fun-ext $ λ vs →
                                 kr r (packᴿ λ _ → refl)

    zip-eq : ∀ (e : Desc I) {σ} (b : ⟦ e ⟧ (Scope (Tm d i)) σ Γ) →
             ⟦ e ⟧ᴿ (Kripkeᴿ Eqᴿ Eqᴿ) (fmap e f b) (fmap e g b) →
             fmap {Y = Kripke 𝓥 𝓒} e f b ≡ fmap e g b
    zip-eq (`σ A d)   (a , b) (refl , zp) = cong (a ,_) (zip-eq (d a) b zp)
    zip-eq (`∎ eq)    refl    zp          = refl
    zip-eq (`X Δ j d) (x , b) (rec  , zp) = cong₂ _,_ (kripke-eq Δ j x rec) (zip-eq d b zp) where


  ren-sem : Fusion d Ren S S
            (λ Γ Δ σ → All Eqᴿ Γ ∘ (select σ)) Eqᴿ Eqᴿ
  ren-sem = FusProp.ren-sem d S alg-fusion

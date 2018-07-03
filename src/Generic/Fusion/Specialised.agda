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

module Generic.Fusion.Specialised where

open import indexed
open import var
open import environment
open import varlike
open import rel
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Zip
open import Generic.Fusion
open import Generic.Identity

open import Size
open import Function
open import Data.Sum
open import Data.Product hiding (,_)
open import Data.List.Base hiding (lookup)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

module _ {I} (d : Desc I) {𝓥 𝓒} (S : Sem d 𝓥 𝓒) where

  sem-ren : Fus (λ σ → ∀[ Eq^R ] ∘ (select σ)) Eq^R Eq^R d Renaming S S
  Fus.quote₁ sem-ren = λ _ t → t
  Fus.vl^𝓥₁ sem-ren = vl^Var
  Fus.th^R   sem-ren = λ σ ρ^R → pack^R (λ v → cong (λ ρ → Sem.th^𝓥 S ρ σ) (lookup^R ρ^R v))
  lookup^R (Fus.>>^R sem-ren {Γ} {Δ} {Θ} {Ξ} {σ} {ρ₁} {ρ₂} {vs} {ws} ρ^R vs^R) v with split Ξ v
  ... | inj₁ vˡ = begin
    lookup (vs >> ρ₁) (injectˡ Δ (lookup (base vl^Var) vˡ))
      ≡⟨ injectˡ->> vs ρ₁ (lookup (base vl^Var) vˡ) ⟩
    lookup vs (lookup (base vl^Var) vˡ)
      ≡⟨ cong (lookup vs) (lookup-base^Var vˡ) ⟩
    lookup vs vˡ
      ≡⟨ lookup^R vs^R vˡ ⟩
    lookup ws vˡ
      ∎
  ... | inj₂ vʳ = begin
    lookup (vs >> ρ₁) (injectʳ Ξ (lookup (base vl^Var) (lookup σ vʳ)))
      ≡⟨ injectʳ->> vs ρ₁ (lookup (base vl^Var) (lookup σ vʳ)) ⟩
    lookup ρ₁ (lookup (base vl^Var) (lookup σ vʳ))
      ≡⟨ cong (lookup ρ₁) (lookup-base^Var (lookup σ vʳ)) ⟩
    lookup ρ₁ (lookup σ vʳ)
      ≡⟨ lookup^R ρ^R vʳ ⟩
    lookup ρ₂ vʳ
      ∎
  Fus.var^R  sem-ren = λ ρ^R v → cong (Sem.var S) (lookup^R ρ^R v)
  Fus.alg^R  sem-ren {Γ} {Δ} {σ} {si} {ρ₁ = ρ₁} {ρ₂} {ρ₃} b ρ^R zp =
    let rew = λ {σ Γ} (t : ⟦ d ⟧ (Scope (Tm d ∞)) σ Γ) →
              `con-inj {I} {σ} {Γ} {d} (≅⇒≡ (RenId.ren-id (`con t) (pack^R λ _ → refl)))
        v₁  = fmap d (Sem.body Renaming ρ₁) b
        v₃  = fmap d (Sem.body S ρ₃) b
    in begin
         Sem.alg S (fmap d (Sem.body S ρ₂) (fmap d (reify vl^Var) v₁))
           ≡⟨ cong (Sem.alg S ∘ (fmap d (Sem.body S ρ₂))) (fmap² d (Sem.body Renaming ρ₁) (reify vl^Var) b) ⟩
         Sem.alg S (fmap d (Sem.body S ρ₂) (fmap d _ b))
           ≡⟨ cong (Sem.alg S) (fmap² d _ _ b) ⟩
         Sem.alg S (fmap d (λ Δ σ → Sem.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ ∘ Sem.body Renaming ρ₁ Δ σ) b)
           ≡⟨ cong (Sem.alg S) (zip-eq d b (subst (λ t → Zip d (Kripke^R Eq^R Eq^R) t _) (fmap² d _ _ b) zp)) ⟩
         Sem.alg S v₃
       ∎

       where

    zip-eq : ∀ (e : Desc I) {σ} (b : ⟦ e ⟧ (Scope (Tm d si)) σ Γ) →
             let f = λ Δ σ → Sem.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ ∘ Sem.body Renaming ρ₁ Δ σ
                 g = Sem.body S ρ₃ in
             Zip e (Kripke^R Eq^R Eq^R) (fmap e f b) (fmap e g b) →
             fmap {Y = Kripke 𝓥 𝓒} e f b ≡ fmap e g b
    zip-eq (`σ A d)   (a , b) (refl , zp) = cong (a ,_) (zip-eq (d a) b zp)
    zip-eq (`∎ eq)    refl    zp          = refl
    zip-eq (`X Δ j d) (x , b) (rec  , zp) = cong₂ _,_ (kripke-eq Δ j x rec) (zip-eq d b zp) where

      kripke-eq : ∀ Δ j x → Kripke^R Eq^R Eq^R Δ j (Sem.body S ρ₂ Δ j (reify vl^Var Δ j (Sem.body Renaming ρ₁ Δ j x))) (Sem.body S ρ₃ Δ j x) →
                 Sem.body S ρ₂ Δ j (reify vl^Var Δ j (Sem.body Renaming ρ₁ Δ j x)) ≡ Sem.body S ρ₃ Δ j x
      kripke-eq []        j x kr = kr
      kripke-eq Δ@(_ ∷ _) j x kr = ifun-ext $ λ Γ → fun-ext $ λ r → fun-ext $ λ vs →
                                   kr r (pack^R λ _ → refl)

        where
          postulate
              fun-ext : ∀ {ℓ ℓ′} {A : Set ℓ} {B : A → Set ℓ′} {f g : (a : A) → B a} →
                        (∀ x → f x ≡ g x) → f ≡ g
              ifun-ext : ∀ {ℓ ℓ′} {A : Set ℓ} {B : A → Set ℓ′} {f g : {a : A} → B a} →
                         (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ g

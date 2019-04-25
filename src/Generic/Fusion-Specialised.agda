module Generic.Fusion-Specialised where

open import indexed
open import var
open import environment
open import varlike
open import rel
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Zip
open import Generic.Fusion
open import Generic.Identity

open import Size
open import Function
open import Data.Sum
open import Data.Product hiding (,_)
open import Data.List.Base
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

module _ {I} (d : Desc I) {𝓥 𝓒} (S : Sem d 𝓥 𝓒) where

  sem-ren : Fus (λ σ → ∀[ Eq^R ] ∘ (select σ)) Eq^R Eq^R d Renaming S S
  Fus.quote₁ sem-ren = λ _ t → t
  Fus.vl^𝓥₁ sem-ren = vl^Var
  Fus.th^R   sem-ren = λ σ ρ^R → pack^R (λ v → cong (λ ρ → Sem.th^𝓥 S ρ σ) (lookup^R ρ^R v))
  lookup^R (Fus.>>^R sem-ren {Γ} {Δ} {Θ} {Ξ} {σ} {ρ₁} {ρ₂} {vs} {ws} ρ^R vs^R) v
    with split Ξ v | split-injectˡ Δ | split-injectʳ Ξ
  ... | inj₁ x | eq | _ =
    let dispatch = [ lookup vs , lookup ρ₁ ]′ in
    begin
      dispatch (split Ξ (injectˡ Δ (lookup (base vl^Var) x)))
        ≡⟨ cong (λ v → dispatch (split Ξ (injectˡ Δ v))) (lookup-base^Var x) ⟩
      dispatch (split Ξ (injectˡ Δ x))
        ≡⟨ cong dispatch (eq x) ⟩
      lookup vs x
        ≡⟨ lookup^R vs^R x ⟩
      lookup ws x
    ∎
  ... | inj₂ y | _ | eq =
    let dispatch = [ lookup vs , lookup ρ₁ ]′ in
    begin
      dispatch (split Ξ (injectʳ Ξ (lookup (base vl^Var) (lookup σ y))))
        ≡⟨ cong dispatch (eq (lookup (base vl^Var) (lookup σ y))) ⟩
      lookup ρ₁ (lookup (base vl^Var) (lookup σ y))
        ≡⟨ cong (lookup ρ₁) (lookup-base^Var _) ⟩
      lookup ρ₁ (lookup σ y)
        ≡⟨ lookup^R ρ^R y ⟩
      lookup ρ₂ y
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


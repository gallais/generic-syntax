module environment {I : Set} where

open import Data.Nat.Base as ℕ
open import Data.List.Base hiding (lookup ; [_])
open import Data.Sum as S
open import Function
open import Relation.Binary.PropositionalEquality as PEq hiding ([_])

open import indexed
open import var hiding (_<$>_)

infix 3 _─Env

record _─Env (Γ : List I) (𝓥 : I ─Scoped) (Δ : List I) : Set where
  constructor pack
  field lookup : ∀ {i} → Var i Γ → 𝓥 i Δ

open _─Env public


Thinning : List I → List I → Set
Thinning Γ Δ = (Γ ─Env) Var Δ


ε : ∀ {𝓥 n} → ([] ─Env) 𝓥 n
lookup ε ()

_<$>_ : {𝓥 𝓦 : I ─Scoped} {Γ Δ Θ : List I} → ({i : I} → 𝓥 i Δ → 𝓦 i Θ) → (Γ ─Env) 𝓥 Δ → (Γ ─Env) 𝓦 Θ
lookup (f <$> ρ) k = f (lookup ρ k)

split : ∀ {Δ} {i : I} Γ → Var i (Γ ++ Δ) → Var i Γ ⊎ Var i Δ
split []      k     = inj₂ k
split (σ ∷ Γ) z     = inj₁ z
split (σ ∷ Γ) (s k) = S.map s id $ split Γ k

split-injectˡ :  (Γ : List I) {Δ : List I} {σ : I} (v : Var σ Δ) → split Δ (injectˡ Γ v) ≡ inj₁ v
split-injectˡ Γ z                               = refl
split-injectˡ Γ (s v) rewrite split-injectˡ Γ v = refl

split-injectʳ : {Γ : List I} (Δ : List I) {σ : I} (v : Var σ Γ) → split Δ (injectʳ Δ v) ≡ inj₂ v
split-injectʳ []      v                           = refl
split-injectʳ (_ ∷ Δ) v rewrite split-injectʳ Δ v = refl

injectˡ-split : ∀ {Δ} {i : I} Γ (v : Var i (Γ ++ Δ)) {k₁ : Var i Γ} → split Γ v ≡ inj₁ k₁ → injectˡ Δ k₁ ≡ v
injectˡ-split []      v     ()
injectˡ-split (σ ∷ Γ) z     refl = refl
injectˡ-split (σ ∷ Γ) (s v) eq with split Γ v | inspect (split Γ) v
injectˡ-split (σ ∷ Γ) (s v) refl | inj₁ _ | PEq.[ eq ] = cong s (injectˡ-split Γ v eq)
injectˡ-split (σ ∷ Γ) (s v) ()   | inj₂ _ | _

injectʳ-split : ∀ {Δ} {i : I} Γ (v : Var i (Γ ++ Δ)) {k₂ : Var i Δ} → split Γ v ≡ inj₂ k₂ → injectʳ Γ k₂ ≡ v
injectʳ-split []      v     refl = refl
injectʳ-split (σ ∷ Γ) z     ()
injectʳ-split (σ ∷ Γ) (s v) eq with split Γ v | inspect (split Γ) v
injectʳ-split (σ ∷ Γ) (s v) ()   | inj₁ _ | _
injectʳ-split (σ ∷ Γ) (s v) refl | inj₂ _ | PEq.[ eq ] = cong s (injectʳ-split Γ v eq)

inject-split : ∀ {Δ} {i : I} Γ (v : Var i (Γ ++ Δ)) → [ injectˡ Δ , injectʳ Γ ]′ (split Γ v) ≡ v
inject-split Γ v with split Γ v | inspect (split Γ) v
... | inj₁ k₁ | PEq.[ eq ] = injectˡ-split Γ v eq
... | inj₂ k₂ | PEq.[ eq ] = injectʳ-split Γ v eq

_>>_ : ∀ {𝓥 Γ Δ Θ} → (Γ ─Env) 𝓥 Θ → (Δ ─Env) 𝓥 Θ → (Γ ++ Δ ─Env) 𝓥 Θ
lookup (ρ₁ >> ρ₂) k = [ lookup ρ₁ , lookup ρ₂ ]′ (split _ k)

injectˡ->> : ∀ {𝓥 Γ Δ Θ i} (ρ₁ : (Γ ─Env) 𝓥 Θ) (ρ₂ : (Δ ─Env) 𝓥 Θ) (v : Var i Γ) →
             lookup (ρ₁ >> ρ₂) (injectˡ Δ v) ≡ lookup ρ₁ v
injectˡ->> {Δ = Δ} ρ₁ ρ₂ v rewrite split-injectˡ Δ v = refl

injectʳ->> : ∀ {𝓥 Γ Δ Θ i} (ρ₁ : (Γ ─Env) 𝓥 Θ) (ρ₂ : (Δ ─Env) 𝓥 Θ) (v : Var i Δ) →
             lookup (ρ₁ >> ρ₂) (injectʳ Γ v) ≡ lookup ρ₂ v
injectʳ->> {Γ = Γ} ρ₁ ρ₂ v rewrite split-injectʳ Γ v = refl

infixl 10 _∙_
_∙_ : ∀ {𝓥 Γ Δ σ} → (Γ ─Env) 𝓥 Δ → 𝓥 σ Δ → (σ ∷ Γ ─Env) 𝓥 Δ
lookup (ρ ∙ v) z    = v
lookup (ρ ∙ v) (s k) = lookup ρ k

select : ∀ {Γ Δ Θ 𝓥} → Thinning Γ Δ → (Δ ─Env) 𝓥 Θ → (Γ ─Env) 𝓥 Θ
lookup (select ren ρ) k = lookup ρ (lookup ren k)

extend : ∀ {Γ σ} → Thinning Γ (σ ∷ Γ)
extend = pack s


□ : (List I → Set) → (List I → Set)
(□ T) Γ = [ Thinning Γ ⟶ T ]

extract    : {T : List I → Set} → [ □ T ⟶ T        ]
duplicate  : {T : List I → Set} → [ □ T ⟶ □ (□ T)  ]

extract t = t (pack id)
duplicate t ρ σ = t (select ρ σ)

join : {T : List I → Set} → [ □ (□ T) ⟶ □ T ]
join = extract


Thinnable : (List I → Set) → Set
Thinnable T = [ T ⟶ □ T ]


th^Var : {i : I} → Thinnable (Var i)
th^Var v ρ = lookup ρ v

th^Env : ∀ {Γ 𝓥} → ({i : I} → Thinnable (𝓥 i)) → Thinnable ((Γ ─Env) 𝓥)
lookup (th^Env th^𝓥 ρ ren) k = th^𝓥 (lookup ρ k) ren

th^□ : {T : List I → Set} → Thinnable (□ T)
th^□ = duplicate

Kripke :  (𝓥 𝓒 : I ─Scoped) → (List I → I ─Scoped)
Kripke 𝓥 𝓒 []  i = 𝓒 i
Kripke 𝓥 𝓒 Γ   i = □ ((Γ ─Env) 𝓥 ⟶ 𝓒 i)

th^Kr : {𝓥 𝓒 : I ─Scoped}
        (Γ : List I) → ({i : I} → Thinnable (𝓒 i)) → {i : I} → Thinnable (Kripke 𝓥 𝓒 Γ i)
th^Kr []       th^𝓒 = th^𝓒
th^Kr (_ ∷ _)  th^𝓒 = th^□

open import Category.Applicative

module _ {𝓥 : I ─Scoped} {A : Set → Set} (app : RawApplicative A) where

 private module A = RawApplicative app
 open A

 traverse : {Γ Δ : List I} → (Γ ─Env) (λ i Γ → A (𝓥 i Γ)) Δ → A ((Γ ─Env) 𝓥 Δ)
 traverse = go _ where

   go : ∀ Γ {Δ} → (Γ ─Env) (λ i Γ → A (𝓥 i Γ)) Δ → A ((Γ ─Env) 𝓥 Δ)
   go []       ρ = pure ε
   go (σ ∷ Γ)  ρ = flip _∙_ A.<$> lookup ρ z ⊛ go Γ (select extend ρ)


\begin{code}
module Generic.Examples.POPLMark2 where

open import var hiding (_<$>_)
open import rel
open import varlike
open import indexed
open import environment
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Fusion
open import Data.Unit
open import Agda.Builtin.Bool
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Data.Product hiding (,_)
open import Agda.Builtin.List
open import Size
open import Function

data Type : Set where
  α   : Type
  _⇒_ : Type → Type → Type

TermD : Desc Type
TermD =  `σ (Type × Type) λ { (σ , τ) →
         `X (σ ∷ []) τ (`∎ (σ ⇒ τ))
         `+ `X [] (σ ⇒ τ) (`X [] σ (`∎ τ)) }

infixl 10 _`∙_
pattern `λ t     = `con ((_ , _) , (true , t , refl))
pattern _`∙_ f t = `con ((_ , _) , (false , f , t , refl))

Term : Type ─Scoped
Term = Tm TermD ∞

`id : ∀ {σ} → [ Term (σ ⇒ σ) ]
`id = `λ (`var z)

_[_/0] : ∀ {σ τ} → [ (σ ∷_) ⊢ Term τ ⟶ Term σ ⟶ Term τ ]
t [ u /0] = sub (base vl^Tm ∙ u) t

infix 3 _↝_
data _↝_ : ∀ {σ} → [ Term σ ⟶ Term σ ⟶ κ Set ] where
-- computational
  β    : ∀ {Γ σ τ} {t : Term τ (σ ∷ Γ)} {u : Term σ Γ} → `λ t `∙ u ↝ t [ u /0]
-- structural
  [λ]  : ∀ {Γ σ τ} {t u : Term τ (σ ∷ Γ)} → t ↝ u → `λ t ↝ `λ u
  [∙]₁ : ∀ {Γ σ τ} {f : Term (σ ⇒ τ) Γ} {t u : Term σ Γ} → t ↝ u → f `∙ t ↝ f `∙ u
  [∙]₂ : ∀ {Γ σ τ} {f g : Term (σ ⇒ τ) Γ} {t : Term σ Γ} → f ↝ g → f `∙ t ↝ g `∙ t

ren-invert-∙ : ∀ {σ τ Γ Δ} (u : Term τ Γ) {f : Term (σ ⇒ τ) Δ} {t : Term σ Δ} (ρ : Thinning Γ Δ) →
               f `∙ t ≡ ren ρ u → ∃ λ f′ → ∃ λ t′ → f′ `∙ t′ ≡ u × f ≡ ren ρ f′ × t ≡ ren ρ t′
ren-invert-∙ (`var _)   ρ ()
ren-invert-∙ (`λ _)     ρ ()
ren-invert-∙ (f′ `∙ t′) ρ refl = f′ , t′ , refl , refl , refl

ren-invert-λ : ∀ {σ τ Γ Δ} (u : Term (σ ⇒ τ) Γ) {b : Term τ (σ ∷ Δ)} (ρ : Thinning Γ Δ) →
               `λ b ≡ ren ρ u → ∃ λ b′ → `λ b′ ≡ u × b ≡ ren (lift vl^Var (σ ∷ []) ρ) b′
ren-invert-λ (`var _) ρ ()
ren-invert-λ (_ `∙ _) ρ ()
ren-invert-λ (`λ b′)  ρ refl = b′ , refl , refl
                                
ren-↝-invert :  ∀ {σ Γ Δ} (t′ : Term σ Γ) {t u : Term σ Δ} (ρ : Thinning Γ Δ) →
                t ≡ ren ρ t′ → t ↝ u → ∃ λ u′ → u ≡ ren ρ u′ × t′ ↝ u′
ren-↝-invert t ρ eq β        =
  let (f′ , t′ , eq∙ , eqf , eqt) = ren-invert-∙ t ρ eq
      (b′ , eqλ , eqb)            = ren-invert-λ f′ ρ eqf
      eqβ : `λ b′ `∙ t′ ≡ t
      eqβ = trans (cong (_`∙ t′) eqλ) eq∙
  in b′ [ t′ /0] , {!!} , subst (_↝ b′ [ t′ /0]) eqβ β
ren-↝-invert t ρ eq ([λ] r)  =
  let (t′ , eqλ , eqt) = ren-invert-λ t ρ eq
      (u′ , eq , r′)   = ren-↝-invert t′ _ eqt r
  in `λ u′ , cong `λ eq , subst (_↝ `λ u′) eqλ ([λ] r′)
ren-↝-invert t ρ eq ([∙]₁ r) =
  let (f′ , t′ , eq∙ , eqf , eqt) = ren-invert-∙ t ρ eq
      (u′ , eq , r′)              = ren-↝-invert t′ ρ eqt r
  in f′ `∙ u′ , cong₂ _`∙_ eqf eq , subst (_↝ f′ `∙ u′) eq∙ ([∙]₁ r′)
ren-↝-invert t ρ eq ([∙]₂ r) = 
  let (f′ , t′ , eq∙ , eqf , eqt) = ren-invert-∙ t ρ eq
      (g′ , eq , r′)              = ren-↝-invert f′ ρ eqf r
  in g′ `∙ t′ , cong₂ _`∙_ eq eqt , subst (_↝ g′ `∙ t′) eq∙ ([∙]₂ r′)

th-↝ : ∀ {σ Γ Δ} {t u : Term σ Γ} (ρ : Thinning Γ Δ) → t ↝ u → ren ρ t ↝ ren ρ u
th-↝ {t = `λ t `∙ u} ρ β =  subst (ren ρ (`λ t `∙ u) ↝_) eq β where

  eq : ren _ t [ ren ρ u /0] ≡ ren ρ (t [ u /0])
  eq = begin
    ren _ t [ ren ρ u /0]               ≡⟨ rensub TermD t _ _ ⟩
    sub {!!} t                          ≡⟨ {!!} ⟩ -- need: sub-ext
    sub (ren ρ <$> (base vl^Tm ∙ u)) t  ≡⟨ sym (subren TermD t _ _) ⟩
    ren ρ (t [ u /0])     ∎

th-↝ ρ ([λ] r)  = [λ] (th-↝ _ r)
th-↝ ρ ([∙]₁ r) = [∙]₁ (th-↝ ρ r)
th-↝ ρ ([∙]₂ r) = [∙]₂ (th-↝ ρ r)

data SN {σ Γ} (t : Term σ Γ) : Set where
  sn : (∀ u → t ↝ u → SN u) → SN t

Unit : Type ─Scoped
Unit _ _ = ⊤

Red : Rel Term Unit -- predicate = binary relation with boring second component
𝓡 : ∀ {σ} → [ Term σ ⟶ κ Set ]

rel Red {α}         t _ = SN t
rel Red {σ ⇒ τ} {Γ} t _ = ∀ {Δ} (ρ : Thinning Γ Δ) {u} → 𝓡 u → 𝓡 (ren ρ t `∙ u)

𝓡 t = rel Red t _

lemma2-1 : ∀ {σ τ Γ} {t : Term (σ ⇒ τ) Γ} {u : Term σ Γ} → 𝓡 t → 𝓡 u → 𝓡 (t `∙ u)
lemma2-1 T U = let TU = T (base vl^Var) U
               in subst (λ t → 𝓡 (t `∙ _)) {!!} TU -- need: ren-id

lemma2-2 : ∀ {σ Γ Δ} (ρ : Thinning Γ Δ) (t : Term σ Γ) → SN t → SN (ren ρ t)
lemma2-2 ρ t (sn U) = sn $ λ u r →
  let (u′ , eq , r′) = ren-↝-invert t ρ refl r
  in subst SN (sym eq) $ lemma2-2 ρ u′ (U u′ r′)

lemma2-3 : ∀ σ {Γ Δ} (ρ : Thinning Γ Δ) (t : Term σ Γ) → 𝓡 t → 𝓡 (ren ρ t)
lemma2-3 α       ρ t T = lemma2-2 ρ t T
lemma2-3 (σ ⇒ τ) ρ t T = λ ρ′ U → subst (λ t → 𝓡 (t `∙ _)) (sym (ren² TermD t ρ ρ′)) (T (select ρ ρ′) U)

\end{code}

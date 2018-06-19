module problem where

open import indexed
open import var hiding (_<$>_)
open import environment
open import rel

open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Data.List.Base hiding ([_])
open import Data.Star

infixr 5 _⇒_
data Type : Set where
  ♭   : Type
  _⇒_ : Type → Type → Type

data Source : Type ─Scoped where
  var : ∀ {σ}   → [ Var σ                        ⟶ Source σ       ]
  lam : ∀ {σ τ} → [ (σ ∷_) ⊢ Source τ            ⟶ Source (σ ⇒ τ) ]
  app : ∀ {σ τ} → [ Source (σ ⇒ τ) ⟶ Source σ    ⟶ Source τ       ]
  def : ∀ {σ τ} → [ Source σ ⟶ (σ ∷_) ⊢ Source τ ⟶ Source τ       ]

th^S : ∀ {σ} → Thinnable (Source σ)
th^S (var v)   ρ = var (lookup ρ v)
th^S (lam b)   ρ = lam (th^S b (th^Env th^Var ρ extend ∙ z))
th^S (app f t) ρ = app (th^S f ρ) (th^S t ρ)
th^S (def e t) ρ = def (th^S e ρ) (th^S t (th^Env th^Var ρ extend ∙ z))

sub^S : ∀ {Γ Δ σ} → Source σ Γ → (Γ ─Env) Source Δ → Source σ Δ
sub^S (var v)   ρ = lookup ρ v
sub^S (lam b)   ρ = lam (sub^S b (th^Env th^S ρ extend ∙ var z))
sub^S (app f t) ρ = app (sub^S f (pack (lookup ρ))) (sub^S t (pack (lookup ρ)))
sub^S (def e t) ρ = def (sub^S e ρ) (sub^S t (th^Env th^S ρ extend ∙ var z))

data Target : Type ─Scoped where
  var : ∀ {σ}   → [ Var σ                     ⟶ Target σ       ]
  lam : ∀ {σ τ} → [ (σ ∷_) ⊢ Target τ         ⟶ Target (σ ⇒ τ) ]
  app : ∀ {σ τ} → [ Target (σ ⇒ τ) ⟶ Target σ ⟶ Target τ       ]

th^T : ∀ {σ} → Thinnable (Target σ)
th^T (var v)   ρ = var (lookup ρ v)
th^T (lam b)   ρ = lam (th^T b (th^Env th^Var ρ extend ∙ z))
th^T (app f t) ρ = app (th^T f ρ) (th^T t ρ)

sub^T : ∀ {Γ Δ σ} → Target σ Γ → (Γ ─Env) Target Δ → Target σ Δ
sub^T (var v)   ρ = lookup ρ v
sub^T (lam b)   ρ = lam (sub^T b (th^Env th^T ρ extend ∙ var z))
sub^T (app f t) ρ = app (sub^T f (pack (lookup ρ))) (sub^T t (pack (lookup ρ)))

elab : ∀ {Γ Δ} → (Γ ─Env) Target Δ → ∀ {σ} → Source σ Γ → Target σ Δ
elab ρ (var v)   = lookup ρ v
elab ρ (lam b)   = lam (elab (th^Env th^T ρ extend ∙ var z) b)
elab ρ (app f t) = app (elab ρ f) (elab ρ t)
elab ρ (def d t) = elab (ρ ∙ elab ρ d) t

infix 1 _⊢_∋_↝S_
data _⊢_∋_↝S_ : ∀ Γ σ → Source σ Γ → Source σ Γ → Set where
-- computation
  β    : ∀ {Γ σ τ} (b : Source τ (σ ∷ Γ)) u → Γ ⊢ τ ∋ app (lam b) u ↝S sub^S b (pack var ∙ u)
  ζ    : ∀ {Γ σ τ} e (t : Source τ (σ ∷ Γ)) → Γ ⊢ τ ∋ def e t ↝S sub^S t (pack var ∙ e)
-- structural
  lam  : ∀ {Γ σ τ b c} → (σ ∷ Γ) ⊢ τ ∋ b ↝S c → Γ ⊢ σ ⇒ τ ∋ lam b ↝S lam c
  appl : ∀ {Γ σ τ f g} → Γ ⊢ σ ⇒ τ ∋ f ↝S g → ∀ t → Γ ⊢ τ ∋ app f t ↝S app g t
  appr : ∀ {Γ σ τ t u} f → Γ ⊢ σ ∋ t ↝S u → Γ ⊢ τ ∋ app f t ↝S app f u

infix 1 _⊢_∋_↝T_
data _⊢_∋_↝T_ : ∀ Γ σ → Target σ Γ → Target σ Γ → Set where
-- computation
  β    : ∀ {Γ σ τ} (b : Target τ (σ ∷ Γ)) u → Γ ⊢ τ ∋ app (lam b) u ↝T sub^T b (pack var ∙ u)
-- structural
  lam  : ∀ {Γ σ τ b c} → (σ ∷ Γ) ⊢ τ ∋ b ↝T c → Γ ⊢ σ ⇒ τ ∋ lam b ↝T lam c
  appl : ∀ {Γ σ τ f g} → Γ ⊢ σ ⇒ τ ∋ f ↝T g → ∀ t → Γ ⊢ τ ∋ app f t ↝T app g t
  appr : ∀ {Γ σ τ t u} f → Γ ⊢ σ ∋ t ↝T u → Γ ⊢ τ ∋ app f t ↝T app f u

_⊢_∋_↝⋆T_ : ∀ Γ σ → Target σ Γ → Target σ Γ → Set
Γ ⊢ σ ∋ t ↝⋆T u = Star (Γ ⊢ σ ∋_↝T_) t u

↝⋆T^R : Rel Target Target
rel ↝⋆T^R = _ ⊢ _ ∋_↝⋆T_

th-th^T : ∀ {Γ Δ Θ σ} (t : Target σ Γ) {ρ₁ ρ₃} {ρ₂ : Thinning Δ Θ} →
          ∀[ Eq^R ] (select ρ₁ ρ₂) ρ₃ → th^T (th^T t ρ₁) ρ₂ ≡ th^T t ρ₃
th-th^T (var v)   ρ^R = cong var (lookup^R ρ^R v)
th-th^T (app f t) ρ^R = cong₂ app (th-th^T f ρ^R) (th-th^T t ρ^R)
th-th^T (lam b)   ρ^R = cong lam $ th-th^T b $ pack^R λ where
  z     → refl
  (s v) → cong (λ v → th^Var v extend) (lookup^R ρ^R v)

th-sub^T : ∀ {Γ Δ Θ σ} (t : Target σ Γ) {ρ₁ ρ₃} {ρ₂ : (Δ ─Env) Target Θ} →
           ∀[ Eq^R ] (select ρ₁ ρ₂) ρ₃ → sub^T (th^T t ρ₁) ρ₂ ≡ sub^T t ρ₃
th-sub^T (var v)   ρ^R = lookup^R ρ^R v
th-sub^T (app f t) ρ^R = cong₂ app (th-sub^T f ρ^R) (th-sub^T t ρ^R)
th-sub^T (lam b)   ρ^R = cong lam $ th-sub^T b $ pack^R λ where
  z     → refl
  (s v) → cong (λ t → th^T t extend) (lookup^R ρ^R v)

sub-th^T : ∀ {Γ Δ Θ σ} (t : Target σ Γ) {ρ₁ ρ₃} {ρ₂ : Thinning Δ Θ} →
           ∀[ Eq^R ] (th^Env th^T ρ₁ ρ₂) ρ₃ → th^T (sub^T t ρ₁) ρ₂ ≡ sub^T t ρ₃
sub-th^T (var v)   ρ^R = lookup^R ρ^R v
sub-th^T (app f t) ρ^R = cong₂ app (sub-th^T f ρ^R) (sub-th^T t ρ^R)
sub-th^T (lam b) {ρ₁} {ρ₃} {ρ₂} ρ^R = cong lam $ sub-th^T b $ pack^R λ where
  z     → refl
  (s v) → begin
    th^T (th^T (lookup ρ₁ v) extend) (th^Env th^Var ρ₂ extend ∙ z)
      ≡⟨ th-th^T (lookup ρ₁ v) (pack^R λ v → refl) ⟩
    th^T (lookup ρ₁ v) (select extend (th^Env th^Var ρ₂ extend ∙ z))
      ≡⟨ sym (th-th^T (lookup ρ₁ v) (pack^R λ { z → refl ; (s v) → refl })) ⟩
    th^T (th^T (lookup ρ₁ v) ρ₂) extend
      ≡⟨ cong (λ ρ → th^T ρ extend) (lookup^R ρ^R v) ⟩
    th^T (lookup ρ₃ v) extend
      ∎

th^↝T : ∀ {Γ Δ σ t u} (ρ : Thinning Γ Δ) → Γ ⊢ σ ∋ t ↝T u → Δ ⊢ σ ∋ th^T t ρ ↝T th^T u ρ
th^↝T ρ (lam r)    = lam (th^↝T _ r)
th^↝T ρ (appl r t) = appl (th^↝T ρ r) _
th^↝T ρ (appr f r) = appr _ (th^↝T ρ r)
th^↝T ρ (β b u)    = cast $ β (th^T b (th^Env th^Var ρ extend ∙ z)) (th^T u ρ) where

  eq : sub^T (th^T b (th^Env th^Var ρ extend ∙ z)) (pack var ∙ th^T u ρ) ≡ th^T (sub^T b (pack var ∙ u)) ρ
  eq = begin
    sub^T (th^T b (th^Env th^Var ρ extend ∙ z)) (pack var ∙ th^T u ρ)
      ≡⟨ th-sub^T b (pack^R (λ k → refl)) ⟩
    sub^T b (select (th^Env th^Var ρ extend ∙ z) (pack var ∙ th^T u ρ))
      ≡⟨ sym (sub-th^T b (pack^R λ { z → refl ; (s v) → refl })) ⟩
    th^T (sub^T b (pack var ∙ u)) ρ
      ∎

  cast = subst (_ ⊢ _ ∋ app (lam _) _ ↝T_) eq

th^↝⋆T : ∀ {Γ Δ σ t u} (ρ : Thinning Γ Δ) → Γ ⊢ σ ∋ t ↝⋆T u → Δ ⊢ σ ∋ th^T t ρ ↝⋆T th^T u ρ
th^↝⋆T ρ Star.ε   = Star.ε
th^↝⋆T ρ (r ◅ rs) = th^↝T ρ r ◅ th^↝⋆T ρ rs

{-
sub^↝⋆T : ∀ {Γ Δ σ} t {ρ ρ′ : (Γ ─Env) Target Δ} → ∀[ ↝⋆T^R ] ρ ρ′ → Δ ⊢ σ ∋ sub^T t ρ ↝⋆T sub^T t ρ′
sub^↝⋆T t ρ^R = {!!}
-}

elab^↝⋆T : ∀ {Γ Δ σ} {ρ ρ′ : (Γ ─Env) Target Δ} → ∀[ ↝⋆T^R ] ρ ρ′ →
           ∀ t → Δ ⊢ σ ∋ elab ρ t ↝⋆T elab ρ′ t
elab^↝⋆T ρ^R (var v)   = lookup^R ρ^R v
elab^↝⋆T ρ^R (lam b)   = gmap lam lam (elab^↝⋆T ((th^↝⋆T extend <$>^R ρ^R) ∙^R Star.ε) b)
elab^↝⋆T ρ^R (app f t) = gmap (λ f → app f _) (λ r → appl r _) (elab^↝⋆T ρ^R f)
                      ◅◅ gmap (app _) (appr _) (elab^↝⋆T ρ^R t)
elab^↝⋆T ρ^R (def e t) = elab^↝⋆T (ρ^R ∙^R elab^↝⋆T ρ^R e) t

simulation : ∀ {Γ Δ σ t u ρ ρ′} → ∀[ ↝⋆T^R ] ρ ρ′ → Γ ⊢ σ ∋ t ↝S u →
             Δ ⊢ σ ∋ elab ρ t ↝⋆T elab ρ′ u
simulation ρ^R (β b u)    = {!!} -- need elab-sub fusion?
simulation ρ^R (ζ e t)    = {!!}
simulation ρ^R (lam r)    = gmap lam lam (simulation ((th^↝⋆T extend <$>^R ρ^R) ∙^R Star.ε) r)
simulation ρ^R (appl r t) = gmap (λ f → app f _) (λ r → appl r _) (simulation ρ^R r)
                         ◅◅ gmap (app _) (appr _) (elab^↝⋆T ρ^R t)
simulation ρ^R (appr f r) = gmap (app _) (appr _) (simulation ρ^R r)
                         ◅◅ gmap (λ f → app f _) (λ r → appl r _) (elab^↝⋆T ρ^R f)

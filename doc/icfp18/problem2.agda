module problem2 where

open import indexed
open import var hiding (_<$>_)
open import varlike
open import environment as E
open import rel

open import Generic.Syntax
open import Generic.Semantics
open import Generic.Simulation as S
open import Generic.Fusion as F
open import Generic.Identity

open import Data.Sum
open import Data.Product hiding (,_)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Data.List.Base hiding ([_])
open import Data.Star

infixr 5 _⇒_
data Type : Set where
  ♭   : Type
  _⇒_ : Type → Type → Type

data `Source : Set where
  Lam App Def : Type → Type → `Source

Source : Desc Type
Source = `σ `Source $ λ where
  (Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ ⇒ τ))
  (App σ τ) → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ))
  (Def σ τ) → `X [] σ (`X (σ ∷ []) τ (`∎ τ))

S : Type ─Scoped
S = Tm Source _

data `Target : Set where
  Lam App : Type → Type → `Target

Target : Desc Type
Target = `σ `Target $ λ where
  (Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ ⇒ τ))
  (App σ τ) → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ))

T : Type ─Scoped
T = Tm Target _

pattern lam' b = (Lam _ _ , b , refl)
pattern lam  b = `con (lam' b)
pattern app' f t = (App _ _ , f , t , refl)
pattern app  f t = `con (app' f t)
pattern def' e t = (Def _ _ , e , t , refl)
pattern def  e t = `con (def' e t)

Elab : Sem Source T T
Sem.th^𝓥  Elab = th^Tm
Sem.var    Elab = id
Sem.alg    Elab = λ where
  (lam' b)   → lam (reify^Tm (_ ∷ []) b)
  (app' f t) → app f t
  (def' e t) → extract t (E.ε ∙ e)

elab :  ∀ {Γ Δ} → (Γ ─Env) T Δ → ∀ {σ} → S σ Γ → T σ Δ
elab ρ t = Sem.sem Elab ρ t

infix 21 0↦_
0↦_ : ∀ {Γ σ} {d : Desc Type} → Tm d _ σ Γ → (σ ∷ Γ ─Env) (Tm d _) Γ
lookup (0↦ t) z     = t
lookup (0↦ t) (s v) = `var v

infix 1 _⊢_∋_↝S_
data _⊢_∋_↝S_ : ∀ Γ σ → S σ Γ → S σ Γ → Set where
-- computation
  `β    : ∀ {Γ σ τ} (b : S τ (σ ∷ Γ)) u → Γ ⊢ τ ∋ app (lam b) u ↝S sub (0↦ u) b
  `ζ    : ∀ {Γ σ τ} e (t : S τ (σ ∷ Γ)) → Γ ⊢ τ ∋ def e t ↝S sub (0↦ e) t
-- structural
  `lam  : ∀ {Γ σ τ b c} → (σ ∷ Γ) ⊢ τ ∋ b ↝S c → Γ ⊢ σ ⇒ τ ∋ lam b ↝S lam c
  `appl : ∀ {Γ σ τ f g} → Γ ⊢ σ ⇒ τ ∋ f ↝S g → ∀ t → Γ ⊢ τ ∋ app f t ↝S app g t
  `appr : ∀ {Γ σ τ t u} f → Γ ⊢ σ ∋ t ↝S u → Γ ⊢ τ ∋ app f t ↝S app f u

infix 1 _⊢_∋_↝T_
data _⊢_∋_↝T_ : ∀ Γ σ → T σ Γ → T σ Γ → Set where
-- computation
  `β    : ∀ {Γ σ τ} (b : T τ (σ ∷ Γ)) u → Γ ⊢ τ ∋ app (lam b) u ↝T b [ u /0]
-- structural
  `lam  : ∀ {Γ σ τ b c} → (σ ∷ Γ) ⊢ τ ∋ b ↝T c → Γ ⊢ σ ⇒ τ ∋ lam b ↝T lam c
  `appl : ∀ {Γ σ τ f g} → Γ ⊢ σ ⇒ τ ∋ f ↝T g → ∀ t → Γ ⊢ τ ∋ app f t ↝T app g t
  `appr : ∀ {Γ σ τ t u} f → Γ ⊢ σ ∋ t ↝T u → Γ ⊢ τ ∋ app f t ↝T app f u

_⊢_∋_↝⋆T_ : ∀ Γ σ → T σ Γ → T σ Γ → Set
Γ ⊢ σ ∋ t ↝⋆T u = Star (Γ ⊢ σ ∋_↝T_) t u

↝⋆T^R : Rel T T
rel ↝⋆T^R = _ ⊢ _ ∋_↝⋆T_

th^↝T : ∀ {Γ Δ σ t u} (ρ : Thinning Γ Δ) →
        Γ ⊢ σ ∋ t ↝T u → Δ ⊢ σ ∋ th^Tm t ρ ↝T th^Tm u ρ
th^↝T ρ (`lam r)    = `lam (th^↝T _ r)
th^↝T ρ (`appl r t) = `appl (th^↝T ρ r) _
th^↝T ρ (`appr f r) = `appr _ (th^↝T ρ r)
th^↝T ρ (`β b u)    = cast $ `β (th^Tm b _) (th^Tm u ρ)
  where cast = subst (_ ⊢ _ ∋ th^Tm (app (lam b) u) ρ ↝T_) (renβ Target b (E.ε ∙ u) ρ)

th^↝⋆T : ∀ {Γ Δ σ t u} (ρ : Thinning Γ Δ) →
         Γ ⊢ σ ∋ t ↝⋆T u → Δ ⊢ σ ∋ th^Tm t ρ ↝⋆T th^Tm u ρ
th^↝⋆T ρ Star.ε   = Star.ε
th^↝⋆T ρ (r ◅ rs) = th^↝T ρ r ◅ th^↝⋆T ρ rs

Elab^↝⋆T : Sim ↝⋆T^R ↝⋆T^R Source Elab Elab
Sim.th^R  Elab^↝⋆T = th^↝⋆T
Sim.var^R Elab^↝⋆T = id
Sim.alg^R Elab^↝⋆T = λ where
  (app' f t) ρ^R (refl , f^r , t^r , _) → gmap (λ f → app f _) (λ r → `appl r _) f^r
                                       ◅◅ gmap (app _) (`appr _) t^r
  (lam' b)   ρ^R (refl , b^r , _)       → gmap lam `lam (b^r _ (pack^R (λ v → Star.ε)))
  (def' e t) ρ^R (refl , e^r , t^r , _) → t^r _ (ε^R ∙^R e^r)

ThElab : Fus (λ ρ₁ ρ₂ → ∀[ Eq^R ] (select ρ₁ ρ₂)) Eq^R Eq^R
             Source Renaming Elab Elab
Fus.quote₁ ThElab = λ σ t → t
Fus.vl^𝓥₁ ThElab = vl^Var
Fus.th^R   ThElab = λ σ ρ^R → pack^R (λ k → cong (ren σ) (lookup^R ρ^R k))
Fus.>>^R   ThElab = thBodyEnv
Fus.var^R  ThElab = λ ρ^R → lookup^R ρ^R
Fus.alg^R  ThElab (app' f t) ρ^R (refl , eq^f , eq^t , _) = cong₂ app eq^f eq^t
Fus.alg^R  ThElab (def' e t) ρ^R (refl , eq^e , eq^t , _) = eq^t (pack id) (ε^R ∙^R eq^e)
Fus.alg^R  ThElab (lam' b)   ρ^R (refl , eq^b , _)        = cong lam (eq^b _ refl^R)

th-elab : ∀ {Γ Δ Θ σ} (t : S σ Γ) {ρ₁ ρ₃} {ρ₂ : (Δ ─Env) T Θ} →
          ∀[ Eq^R ] (select ρ₁ ρ₂) ρ₃ → elab ρ₂ (th^Tm t ρ₁) ≡ elab ρ₃ t
th-elab t ρ^R = Fus.fus ThElab ρ^R t

elab-th : ∀ {Γ Δ Θ σ} (t : S σ Γ) {ρ₁ ρ₃} {ρ₂ : Thinning Δ Θ} →
          ∀[ Eq^R ] (th^Env th^Tm ρ₁ ρ₂) ρ₃ → th^Tm (elab ρ₁ t) ρ₂ ≡ elab ρ₃ t
elab-th (`var v)   ρ^R = lookup^R ρ^R v
elab-th (app f t) ρ^R = cong₂ app (elab-th f ρ^R) (elab-th t ρ^R)
elab-th (lam b) {ρ₁} {ρ₃} {ρ₂} ρ^R = cong lam $ elab-th b $ pack^R λ where
  z     → refl
  (s v) → begin
    th^Tm (th^Tm (lookup ρ₁ v) _) _
      ≡⟨ ren² Target (lookup ρ₁ v) (freshʳ vl^Var (_ ∷ [])) _ ⟩
    th^Tm (lookup ρ₁ v) _
      ≡⟨ sym (Fus.fus (Ren² Target) eq^R (lookup ρ₁ v)) ⟩
    th^Tm (th^Tm (lookup ρ₁ v) ρ₂) (freshʳ vl^Var (_ ∷ []))
      ≡⟨ cong (ren _) (lookup^R ρ^R v) ⟩
    th^Tm (lookup ρ₃ v) (freshʳ vl^Var (_ ∷ []))
      ∎ where

   eq^R : ∀[ Eq^R ] (select ρ₂ (freshʳ vl^Var (_ ∷ []))) _
   lookup^R eq^R k = cong (s ∘ lookup (base vl^Var) ∘ lookup ρ₂)
                   $ sym $ lookup-base^Var k
elab-th (def e t) {ρ₁} {ρ₃} {ρ₂} ρ^R = elab-th t $ pack^R λ where
  z     → elab-th e ρ^R
  (s v) → begin
    th^Tm (th^Tm (lookup ρ₁ v) (pack id)) ρ₂
      ≡⟨ Fus.fus (Ren² Target) (pack^R (λ v → refl)) (lookup ρ₁ v) ⟩
    th^Tm (lookup ρ₁ v) ρ₂
      ≡⟨ lookup^R ρ^R v ⟩
    lookup ρ₃ v
      ≡⟨ sym (ren-id′ (lookup ρ₃ v)) ⟩
    th^Tm (lookup ρ₃ v) (pack id)
      ∎

SubElab : Fus (λ ρ₁ ρ₂ → ∀[ Eq^R ] (elab ρ₂ <$> ρ₁)) Eq^R Eq^R
          Source Substitution Elab Elab
Fus.quote₁ SubElab = λ σ t → t
Fus.vl^𝓥₁ SubElab = vl^Tm
Fus.th^R   SubElab {ρ₁ = ρ₁} {ρ₂} {ρ₃} = λ σ ρ^R → pack^R λ v → begin
  elab (th^Env th^Tm ρ₂ σ) (lookup ρ₁ v)
    ≡⟨ sym $ elab-th (lookup ρ₁ v) refl^R ⟩
  ren σ (elab ρ₂ (lookup ρ₁ v))
    ≡⟨ cong (ren σ) (lookup^R ρ^R v) ⟩
  ren σ (lookup ρ₃ v)
    ∎
Fus.>>^R   SubElab {ρ₁ = ρ₁} = subBodyEnv Elab ThElab (λ σ t → refl) ρ₁
Fus.var^R  SubElab = λ ρ^R → lookup^R ρ^R
Fus.alg^R  SubElab (app' f t) ρ^R (refl , eq^f , eq^t , _) = cong₂ app eq^f eq^t
Fus.alg^R  SubElab (def' e t) ρ^R (refl , eq^e , eq^t , _) = eq^t (pack id) (ε^R ∙^R eq^e)
Fus.alg^R  SubElab (lam' b)   ρ^R (refl , eq^b , _)        = cong lam (eq^b _ refl^R)

elab-sub : ∀ {Γ Δ Θ σ} (t : S σ Γ) {ρ₁ ρ₃} {ρ₂ : (Δ ─Env) T Θ} →
           ∀[ Eq^R ] (sub ρ₂ <$> ρ₁) ρ₃ → sub ρ₂ (elab ρ₁ t) ≡ elab ρ₃ t
elab-sub (`var v)   ρ^R = lookup^R ρ^R v
elab-sub (app f t) ρ^R = cong₂ app (elab-sub f ρ^R) (elab-sub t ρ^R)
elab-sub (lam b) {ρ₁} {ρ₃} {ρ₂} ρ^R = cong lam $ elab-sub b $ pack^R λ where
  z     → refl
  (s v) → begin
    sub _ (th^Tm (lookup ρ₁ v) (freshʳ vl^Var (_ ∷ [])))
      ≡⟨ F.rensub Target (lookup ρ₁ v) _ _ ⟩
    sub _ (lookup ρ₁ v)
      ≡⟨ sym (Fus.fus (SubRen Target) eq^R (lookup ρ₁ v)) ⟩
    th^Tm (sub ρ₂ (lookup ρ₁ v)) _
      ≡⟨ cong (λ t → th^Tm t _) (lookup^R ρ^R v) ⟩
    th^Tm (lookup ρ₃ v) _
      ∎ where

  eq^R : ∀[ Eq^R ] _ _
  lookup^R eq^R v = cong (ren _ ∘ lookup ρ₂) (sym (lookup-base^Var v))

elab-sub (def e t) {ρ₁} {ρ₃} {ρ₂} ρ^R = elab-sub t $ pack^R λ where
  z     → elab-sub e ρ^R
  (s v) → begin
    sub ρ₂ (th^Tm (lookup ρ₁ v) (pack id))
      ≡⟨ cong (sub ρ₂) (ren-id′ (lookup ρ₁ v)) ⟩
    sub ρ₂ (lookup ρ₁ v)
      ≡⟨ lookup^R ρ^R v ⟩
    lookup ρ₃ v
      ≡⟨ sym (ren-id′ (lookup ρ₃ v)) ⟩
    th^Tm (lookup ρ₃ v) (pack id)
      ∎

simulation : ∀ {Γ Δ σ t u ρ ρ′} → ∀[ ↝⋆T^R ] ρ ρ′ → Γ ⊢ σ ∋ t ↝S u →
             Δ ⊢ σ ∋ elab ρ t ↝⋆T elab ρ′ u
simulation {Γ} {Δ} {ρ = ρ} {ρ′} ρ^R (`β b u)    =
    subst (Δ ⊢ _ ∋ _ ↝⋆T_) (sym (Fus.fus SubElab refl^R b))
  $ `β (elab _ b) (elab _ u)
  ◅_ $  subst (Δ ⊢ _ ∋_↝⋆T _) (sym (elab-sub b eq^R))
  $ Sim.sim Elab^↝⋆T ρ∙u^R b where

  eq′^R : ∀[ Eq^R ] (select (freshʳ vl^Var (_ ∷ [])) (elab ρ u /0])) (base vl^Tm)
  lookup^R eq′^R z     = refl
  lookup^R eq′^R (s v) = cong (ren extend ∘ lookup (base vl^Tm)) (lookup-base^Var v)

  eq^R : ∀[ Eq^R ] (sub (elab ρ u /0]) <$> (freshˡ vl^Tm Δ {_ ∷ []} >> _))
                   (elab ρ <$> (0↦ u))
  lookup^R eq^R z     = refl
  lookup^R eq^R (s v) = begin
    sub (elab ρ u /0]) (ren (freshʳ vl^Var (_ ∷ [])) (lookup ρ v))
      ≡⟨ Fus.fus (F.RenSub Target) eq′^R (lookup ρ v) ⟩
    sub (base vl^Tm) (lookup ρ v)
      ≡⟨ sub-id (lookup ρ v) ⟩
    lookup ρ v
      ∎

  ρ∙u^R : ∀[ ↝⋆T^R ] (elab ρ <$> (0↦ u)) (elab ρ′ <$> (0↦ u))
  lookup^R ρ∙u^R z     = Sim.sim Elab^↝⋆T ρ^R u
  lookup^R ρ∙u^R (s v) = lookup^R ρ^R v

simulation {ρ = ρ} {ρ′} ρ^R (`ζ e t) =
  subst (_ ⊢ _ ∋ _ ↝⋆T_) (sym (Fus.fus SubElab refl^R t))
  $ Sim.sim Elab^↝⋆T ρ′^R t where

  ρ′^R : ∀[ ↝⋆T^R ] ((E.ε ∙ elab ρ e) >> th^Env th^Tm ρ (pack id)) (elab ρ′ <$> (0↦ e))
  lookup^R ρ′^R k with split (_ ∷ []) k
  ... | inj₁ z  = Sim.sim Elab^↝⋆T ρ^R e
  ... | inj₁ (s ())
  ... | inj₂ kʳ = subst (_ ⊢ _ ∋_↝⋆T _) (sym (ren-id′ (lookup ρ kʳ))) (lookup^R ρ^R kʳ)

simulation {Γ} {Δ} {ρ = ρ} {ρ′} ρ^R (`lam r) = gmap lam `lam (simulation ρ′^R r) where

  ρ′^R : ∀[ ↝⋆T^R ] (freshˡ vl^Tm Δ {_ ∷ []} >> th^Env th^Tm ρ (freshʳ vl^Var (_ ∷ [])))
                    (freshˡ vl^Tm Δ {_ ∷ []} >> th^Env th^Tm ρ′ (freshʳ vl^Var (_ ∷ [])))
  lookup^R ρ′^R k with split (_ ∷ []) k
  ... | inj₁ kˡ = Star.ε
  ... | inj₂ kʳ = th^↝⋆T (th^Env th^Var (base vl^Var) extend) (lookup^R ρ^R kʳ)

simulation ρ^R (`appl r t) =
     gmap (λ f → app f _) (λ r → `appl r _) (simulation ρ^R r)
  ◅◅ gmap (app _) (`appr _) (Sim.sim Elab^↝⋆T ρ^R t)
simulation ρ^R (`appr f r) =
    gmap (app _) (`appr _) (simulation ρ^R r)
 ◅◅ gmap (λ f → app f _) (λ r → `appl r _) (Sim.sim Elab^↝⋆T ρ^R f)

\begin{code}
module Generic.Examples.POPLMark2 where

open import Generic hiding (_×_)

open import Agda.Builtin.List
open import Data.Product hiding (,_)
open import Data.Star as S using (Star)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_]); open ≡-Reasoning

data Type : Set where
  α   : Type
  _⇒_ : Type → Type → Type

data TermC : Set where
  Lam : Type → Type → TermC
  App : Type → Type → TermC

TermD : Desc Type
TermD =  `σ TermC λ { (Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ ⇒ τ))
                    ; (App σ τ) → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ)) }

infixl 10 _`∙_
pattern `λ' b     = (Lam _ _ , b , refl)
pattern _`∙'_ f t = (App _ _ , f , t , refl)
pattern `λ  b     = `con (`λ' b)
pattern _`∙_ f t  = `con (f `∙' t)

{-# DISPLAY syn.`con (Lam _ _ , b , refl)      = `λ b   #-}
{-# DISPLAY syn.`con (App _ _ , f , t , refl) = f `∙ t #-}

Term : Type ─Scoped
Term = Tm TermD _

infix 3 _↝_ _↝⋆_
data _↝_ : ∀ {σ} → [ Term σ ⟶ Term σ ⟶ κ Set ] where
-- computational
  β    : ∀ {Γ σ τ} (t : Term τ (σ ∷ Γ)) (u : Term σ Γ) → `λ t `∙ u ↝ t [ u /0]
-- structural
  [λ]  : ∀ {Γ σ τ} {t u : Term τ (σ ∷ Γ)} → t ↝ u → `λ t ↝ `λ u
  [∙]₁ : ∀ {Γ σ τ} (f : Term (σ ⇒ τ) Γ) {t u : Term σ Γ} → t ↝ u → f `∙ t ↝ f `∙ u
  [∙]₂ : ∀ {Γ σ τ} {f g : Term (σ ⇒ τ) Γ} → f ↝ g → (t : Term σ Γ) → f `∙ t ↝ g `∙ t

_↝⋆_ : ∀ {σ} → [ Term σ ⟶ Term σ ⟶ κ Set ]
_↝⋆_ = Star _↝_

th^↝ : ∀ {σ Γ Δ} {t u : Term σ Γ} (ρ : Thinning Γ Δ) → t ↝ u → ren ρ t ↝ ren ρ u
th^↝ ρ (β t u)    = subst (ren ρ (`λ t `∙ u) ↝_) (sym $ renβ TermD t u ρ) (β _ _)
th^↝ ρ ([λ] r)    = [λ] (th^↝ _ r)
th^↝ ρ ([∙]₁ f r) = [∙]₁ (ren ρ f) (th^↝ ρ r)
th^↝ ρ ([∙]₂ r t) = [∙]₂ (th^↝ ρ r) (ren ρ t)

sub^↝ : ∀ {σ Γ Δ} {t u : Term σ Γ} (ρ : (Γ ─Env) Term Δ) → t ↝ u → sub ρ t ↝ sub ρ u
sub^↝ ρ (β t u)    = subst (sub ρ (`λ t `∙ u) ↝_) (sym $ subβ TermD t u ρ) (β (sub _ t) (sub ρ u))
sub^↝ ρ ([λ] r)    = [λ] (sub^↝ _ r)
sub^↝ ρ ([∙]₁ f r) = [∙]₁ (sub ρ f) (sub^↝ ρ r)
sub^↝ ρ ([∙]₂ r t) = [∙]₂ (sub^↝ ρ r) (sub ρ t)

sub^↝⋆ : ∀ {σ Γ Δ} (t : Term σ Γ) {ρ ρ′ : (Γ ─Env) Term Δ} → rel.∀[ mkRel _↝⋆_ ] ρ ρ′ → sub ρ t ↝⋆ sub ρ′ t
sub^↝⋆ t ρ^R = Sim.sim sim ρ^R t where

  sim : Sim (mkRel _↝⋆_) (mkRel _↝⋆_) TermD Substitution Substitution
  Sim.th^R  sim = λ ρ → S.gmap _ (th^↝ ρ)
  Sim.var^R sim = id
  Sim.alg^R sim = λ
    { (f `∙' t) {ρ₁} {ρ₂} ρ^R (refl , f^R , t^R , _) → S.gmap (_`∙ sub ρ₁ t) (λ f → [∙]₂ f (sub ρ₁ t)) f^R
                                                  S.◅◅ S.gmap (sub ρ₂ f `∙_) ([∙]₁ (sub ρ₂ f)) t^R
    ; (`λ' b) ρ^R (refl , b^R , _) → S.gmap `λ [λ] (b^R _ (pack^R (λ _ → S.ε))) }

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
ren-↝-invert {Γ = Γ} {Δ} t ρ eq (β {σ = σ} b u) =
  let (f′ , t′ , eq∙ , eqf , eqt) = ren-invert-∙ t ρ eq
      (b′ , eqλ , eqb)            = ren-invert-λ f′ ρ eqf
      eqβ : `λ b′ `∙ t′ ≡ t
      eqβ = trans (cong (_`∙ t′) eqλ) eq∙

      eq : b [ u /0] ≡ ren ρ (b′ [ t′ /0])
      eq = begin
       b [ u /0]               ≡⟨ cong₂ (λ b u → b [ u /0]) eqb eqt ⟩
       ren _ b′ [ ren ρ t′ /0] ≡⟨ sym (renβ TermD b′ t′ ρ) ⟩
       ren ρ (b′ [ t′ /0])     ∎

  in b′ [ t′ /0] , eq , subst (_↝ b′ [ t′ /0]) eqβ (β b′ t′)
ren-↝-invert t ρ eq ([λ] r)  =
  let (t′ , eqλ , eqt) = ren-invert-λ t ρ eq
      (u′ , eq , r′)   = ren-↝-invert t′ _ eqt r
  in `λ u′ , cong `λ eq , subst (_↝ `λ u′) eqλ ([λ] r′)
ren-↝-invert t ρ eq ([∙]₁ f r) =
  let (f′ , t′ , eq∙ , eqf , eqt) = ren-invert-∙ t ρ eq
      (u′ , eq , r′)              = ren-↝-invert t′ ρ eqt r
  in f′ `∙ u′ , cong₂ _`∙_ eqf eq , subst (_↝ f′ `∙ u′) eq∙ ([∙]₁ f′ r′)
ren-↝-invert t ρ eq ([∙]₂ r u) =
  let (f′ , t′ , eq∙ , eqf , eqt) = ren-invert-∙ t ρ eq
      (g′ , eq , r′)              = ren-↝-invert f′ ρ eqf r
  in g′ `∙ t′ , cong₂ _`∙_ eq eqt , subst (_↝ g′ `∙ t′) eq∙ ([∙]₂ r′ t′)

Closed : (∀ {σ} → [ Term σ ⟶ Term σ ⟶ κ Set ]) → (∀ {σ Γ} → Term σ Γ → Set) → ∀ {σ Γ} → Term σ Γ → Set
Closed red R t = ∀ {u} → red t u → R u

data SN {σ Γ} (t : Term σ Γ) : Set where
  sn : Closed _↝_ SN t → SN t

Closed-SN : ∀ {σ Γ} {t : Term σ Γ} → SN t → Closed _↝_ SN t
Closed-SN (sn t^SN) = t^SN

SN^sub⁻¹ : ∀ {σ Γ Δ} {t : Term σ Γ} (ρ : (Γ ─Env) Term Δ) → SN (sub ρ t) → SN t
SN^sub⁻¹ ρ (sn tρ^SN) = sn (λ r → SN^sub⁻¹ ρ (tρ^SN (sub^↝ ρ r)))

𝓡' : Pred Term
𝓡  : ∀ {σ} → [ Term σ ⟶ κ Set ]

pred 𝓡' {α}         t = SN t
pred 𝓡' {σ ⇒ τ} {Γ} t = ∀ {Δ} (ρ : Thinning Γ Δ) {u} → 𝓡 u → 𝓡 (ren ρ t `∙ u)

𝓡 = pred 𝓡'

SN-`λ : ∀ {σ τ} {Γ} {t : Term τ (σ ∷ Γ)} → SN t → SN (`λ t)
SN-`λ (sn t^R) = sn λ { ([λ] r) → SN-`λ (t^R r) }

lemma2-1 : ∀ {σ τ Γ} {t : Term (σ ⇒ τ) Γ} {u : Term σ Γ} → 𝓡 t → 𝓡 u → 𝓡 (t `∙ u)
lemma2-1 {t = t} T U = subst (λ t → 𝓡 (t `∙ _)) (ren-id t) (T (base vl^Var) U)

lemma2-2 : ∀ {σ Γ Δ} (ρ : Thinning Γ Δ) {t : Term σ Γ} → SN t → SN (ren ρ t)
lemma2-2 ρ (sn u^SN) = sn $ λ r →
  let (_ , eq , r′) = ren-↝-invert _ ρ refl r
  in subst SN (sym eq) $ lemma2-2 ρ (u^SN r′)

lemma2-3 : ∀ σ {Γ Δ} (ρ : Thinning Γ Δ) (t : Term σ Γ) → 𝓡 t → 𝓡 (ren ρ t)
lemma2-3 α       ρ t T = lemma2-2 ρ T
lemma2-3 (σ ⇒ τ) ρ t T = λ ρ′ U → subst (λ t → 𝓡 (t `∙ _)) (sym (ren² TermD t ρ ρ′)) (T (select ρ ρ′) U)

ηexp : ∀ {σ τ} → [ Term (σ ⇒ τ) ⟶ Term (σ ⇒ τ) ]
ηexp t = `λ (ren extend t `∙ `var z)

ηexp^↝ : ∀ {σ τ Γ} {t u : Term (σ ⇒ τ) Γ} → t ↝ u → ηexp t ↝ ηexp u
ηexp^↝ r = [λ] ([∙]₂ (th^↝ extend r) (`var z))

SN-η : ∀ {σ τ Γ} {t : Term (σ ⇒ τ) Γ} → SN (ηexp t) → SN t
SN-η (sn pr) = sn (λ r → SN-η (pr (ηexp^↝ r)))

data NE {σ Γ} : Term σ Γ → Set where
  [var] : (k : Var σ Γ) → NE (`var k)
  _[∙]_ : ∀ {τ} (f : Term (τ ⇒ σ) Γ) (t : Term τ Γ) → NE (f `∙ t)

th^NE : ∀ {σ Γ Δ} {t : Term σ Γ} → NE t → (ρ : Thinning Γ Δ) → NE (ren ρ t)
th^NE ([var] k) ρ = [var] (lookup ρ k)
th^NE (f [∙] t) ρ = ren ρ f [∙] ren ρ t

Closed-𝓡 : ∀ σ {Γ} {t : Term σ Γ} → 𝓡 t → Closed _↝_ 𝓡 t
Closed-𝓡 α       t^R = Closed-SN t^R
Closed-𝓡 (σ ⇒ τ) t^R = λ r ρ u^R → Closed-𝓡 τ (t^R ρ u^R) ([∙]₂ (th^↝ ρ r) _)

Closed⋆-𝓡 : ∀ {σ Γ} {t : Term σ Γ} → 𝓡 t → Closed _↝⋆_ 𝓡 t
Closed⋆-𝓡 t^R Star.ε        = t^R
Closed⋆-𝓡 t^R (r Star.◅ rs) = Closed⋆-𝓡 (Closed-𝓡 _ t^R r) rs

𝓡⇒SN       : ∀ σ {Γ} (t : Term σ Γ) → 𝓡 t → SN t
NE⇒𝓡       : ∀ σ {Γ} (t : Term σ Γ) → NE t → Closed _↝_ 𝓡 t → 𝓡 t
Closed-𝓡-∙ : ∀ {σ τ Γ} {t : Term (σ ⇒ τ) Γ} → NE t → Closed _↝_ 𝓡 t →
              ∀ {a} → 𝓡 a → SN a → Closed _↝_ 𝓡 (t `∙ a)

𝓡⇒SN α       t t^R = t^R
𝓡⇒SN (σ ⇒ τ) t t^R = SN-η ηt where

  𝓡[t∙z] : 𝓡 (ren extend t `∙ `var z)
  𝓡[t∙z] = lemma2-1 (lemma2-3 (σ ⇒ τ) extend t t^R) (NE⇒𝓡 σ (`var z) ([var] z) (λ ()))

  ηt : SN (`λ (ren extend t `∙ `var z))
  ηt = SN-`λ (𝓡⇒SN τ (ren extend t `∙ `var z) 𝓡[t∙z])

NE⇒𝓡 α       t t^NE t^R           = sn t^R
NE⇒𝓡 (σ ⇒ τ) t t^NE t^R ρ {u} u^R = NE⇒𝓡 τ (ren ρ t `∙ u) (ren ρ t [∙] u) tρ∙u^R
  where u^SN   = 𝓡⇒SN σ _ u^R
        tρ^R   : Closed _↝_ 𝓡 (ren ρ t)
        tρ^R r = let (u′ , eq , r′) = ren-↝-invert t ρ refl r
                 in subst 𝓡 (sym eq) (lemma2-3 (σ ⇒ τ) ρ u′ (t^R r′))
        tρ∙u^R : Closed _↝_ 𝓡 (ren ρ t `∙ u)
        tρ∙u^R = Closed-𝓡-∙ (th^NE t^NE ρ) tρ^R u^R u^SN

Closed-𝓡-∙ ()   t^R a^R a^SN      (β t u)
Closed-𝓡-∙ t^NE t^R a^R (sn a^SN) ([∙]₁ t r) =
  NE⇒𝓡 _ _ (t [∙] _) (Closed-𝓡-∙ t^NE t^R (Closed-𝓡 _ a^R r) (a^SN r))
Closed-𝓡-∙ t^NE t^R a^R a^SN      ([∙]₂ r t) = rew $ t^R r (base vl^Var) a^R
  where rew = subst (λ f → 𝓡 (f `∙ _)) (ren-id _)

lemma2-4 : ∀ {Γ Δ Θ} (ρ : Thinning Δ Θ) (vs : (Γ ─Env) Term Δ) →
           pred.∀[ 𝓡' ] vs → pred.∀[ 𝓡' ] (th^Env th^Tm vs ρ)
lemma2-4 ρ vs rs = lemma2-3 _ ρ _ <$>^P rs

Closed-𝓡-β : ∀ {σ τ Γ} {t : Term τ (σ ∷ Γ)} → SN t → ∀ {u} → SN u → 𝓡 (t [ u /0]) → Closed _↝_ 𝓡 (`λ t `∙ u)
𝓡-β        : ∀ {σ τ Γ} {t : Term τ (σ ∷ Γ)} → SN t → ∀ {u} → SN u → 𝓡 (t [ u /0]) → 𝓡 (`λ t `∙ u)

Closed-𝓡-β         t^SN      u^SN      tu^R (β t u)          = tu^R
Closed-𝓡-β {t = t} t^SN      (sn u^SN) tu^R ([∙]₁ f r)       =
  𝓡-β t^SN (u^SN r) (Closed⋆-𝓡 tu^R (sub^↝⋆ t (pack^R (λ _ → S.ε) ∙^R S.return r)))
Closed-𝓡-β         (sn t^SN) u^SN      tu^R ([∙]₂ ([λ] r) u) =
  𝓡-β (t^SN r) u^SN (Closed-𝓡 _ tu^R (sub^↝ (u /0]) r))

𝓡-β t^SN u^SN tu^R = NE⇒𝓡 _ _ (_ [∙] _) (Closed-𝓡-β t^SN u^SN tu^R)

lemma2-5 : ∀ τ {σ Γ} {t : Term τ (σ ∷ Γ)} {u} → SN u → 𝓡 (t [ u /0]) → 𝓡 (`λ t `∙ u)
lemma2-5 τ u^SN tu^R = 𝓡-β (SN^sub⁻¹ (_ /0]) (𝓡⇒SN _ _ tu^R)) u^SN tu^R

theorem2-6 : ∀ {σ Γ Δ} (t : Term σ Γ) (ρ : (Γ ─Env) Term Δ) →
             pred.∀[ 𝓡' ] ρ → 𝓡 (sub ρ t)
theorem2-6 t ρ rs = Fdm.fdm prf rs t where

  prf : Fdm 𝓡' 𝓡' TermD Substitution
  Fdm.th^P  prf = λ ρ → lemma2-3 _ ρ _
  Fdm.var^P prf = id
  Fdm.alg^P prf = alg^P where

    alg^P : ∀ {Γ Δ σ s} (b : ⟦ TermD ⟧ (Scope (Tm TermD s)) σ Γ) {ρ : (Γ ─Env) Term Δ} →
            let v = fmap TermD (Sem.body Substitution ρ) b in
            pred.∀[ 𝓡' ] ρ → All TermD (Kripke^P 𝓡' 𝓡') v → 𝓡 (Sem.alg Substitution v)
    alg^P (f `∙' t) ρ^P (f^P , t^P , _) = subst (𝓡 ∘ (_`∙ _)) (ren-id _) $ f^P (base vl^Var) t^P
    alg^P (`λ' b) {ρ₁} ρ^P (b^P , _) ρ {u} u^P = lemma2-5 _ (𝓡⇒SN _ u u^P) (subst 𝓡 eq (b^P ρ (ε^P ∙^P u^P)))
      where
        ρ′  = lift vl^Var (_ ∷ []) ρ
        ρ₁′ = lift vl^Tm (_ ∷ []) ρ₁

        ρ^R : rel.∀[ VarTm^R ] ρ (select (freshʳ vl^Var (_ ∷ [])) (select ρ′ (u /0])))
        lookup^R ρ^R k = sym $ begin
          lookup (base vl^Tm) (lookup (base vl^Var) (lookup ρ (lookup (base vl^Var) k)))
            ≡⟨ lookup-base^Tm _ ⟩
          `var (lookup (base vl^Var) (lookup ρ (lookup (base vl^Var) k)))
            ≡⟨ cong `var (lookup-base^Var _) ⟩
          `var (lookup ρ (lookup (base vl^Var) k))
            ≡⟨ cong (`var ∘ lookup ρ) (lookup-base^Var k) ⟩
          `var (lookup ρ k) ∎

        ρ^R′ : rel.∀[ Eq^R ] (sub (select ρ′ (u /0])) <$> ρ₁′) ((ε ∙ u) >> th^Env th^Tm ρ₁ ρ)
        lookup^R ρ^R′ z     = refl
        lookup^R ρ^R′ (s k) = begin
          sub (select ρ′ (u /0])) (ren _ (lookup ρ₁ k)) ≡⟨ rensub TermD (lookup ρ₁ k) _ _ ⟩
          sub _ (lookup ρ₁ k)                           ≡⟨ sym $ Sim.sim sim.RenSub ρ^R (lookup ρ₁ k) ⟩
          ren ρ (lookup ρ₁ k) ∎

        eq : sub ((ε ∙ u) >> th^Env th^Tm ρ₁ ρ) b ≡ ren ρ′ (sub ρ₁′ b) [ u /0]
        eq = sym $ begin
              ren ρ′ (sub ρ₁′ b) [ u /0]           ≡⟨ rensub TermD (sub ρ₁′ b) ρ′ (u /0]) ⟩
              sub (select ρ′ (u /0])) (sub ρ₁′ b)  ≡⟨ Fus.fus (Sub² TermD) ρ^R′ b ⟩
              sub ((ε ∙ u) >> th^Env th^Tm ρ₁ ρ) b ∎
\end{code}

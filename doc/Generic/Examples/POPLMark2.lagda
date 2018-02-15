\begin{code}
module Generic.Examples.POPLMark2 where

open import Generic

open import Size
open import Data.Sum as Sum
open import Data.Product as Prod
open import Agda.Builtin.List
open import Data.Product hiding (,_)
open import Data.Star as S using (Star)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_]); open ≡-Reasoning

-- Definition of the language. We define an enumeration `TermC` as the
-- type of constructor instead of using Booleans. This allows us to have
-- a clearer definition as well as storing the needed type arguments in
-- the constructor itself rather than having to use multiple extra `σ
-- constructors in the Desc.

data Type : Set where
  α   : Type
  _⇒_ : Type → Type → Type

data TermC : Set where
  Lam App : Type → Type → TermC

TermD : Desc Type
TermD =  `σ TermC λ where
  (Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ ⇒ τ))
  (App σ τ) → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ))

Term : Type ─Scoped
Term = Tm TermD _

-- We provide handy patterns and DISPLAY rules to hide the encoding
-- our generic-syntax library uses. Unfortunately pattern-synonyms
-- can't yet be typed in Agda.

infixl 10 _`∙_
pattern `λ' b     = (Lam _ _ , b , refl)
pattern _`∙'_ f t = (App _ _ , f , t , refl)
pattern `λ  b     = `con (`λ' b)
pattern _`∙_ f t  = `con (f `∙' t)

{-# DISPLAY syn.`con (Lam _ _ , b , refl)     = `λ b   #-}
{-# DISPLAY syn.`con (App _ _ , f , t , refl) = f `∙ t #-}

-- The Typed Reduction relation can be defined in the usual fashion
-- thanks to the pattern synonyms introduced above. Its reflexive
-- transitive closure is obtained by instantiating the standard
-- library's Star.

infix 3 _↝_ _↝⋆_
data _↝_ : ∀ {σ} → [ Term σ ⟶ Term σ ⟶ κ Set ] where
-- computational
  β    : ∀ {Γ σ τ} (t : Term τ (σ ∷ Γ)) (u : Term σ Γ) → `λ t `∙ u ↝ t [ u /0]
-- structural
  [λ]  : ∀ {Γ σ τ} {t u : Term τ (σ ∷ Γ)} → t ↝ u → `λ t ↝ `λ u
  [∙]₁ : ∀ {Γ σ τ} (f : Term (σ ⇒ τ) Γ) {t u} → t ↝ u → f `∙ t ↝ f `∙ u
  [∙]₂ : ∀ {Γ σ τ} {f g : Term (σ ⇒ τ) Γ} → f ↝ g → ∀ t → f `∙ t ↝ g `∙ t

src : ∀ {σ Γ} {s t : Term σ Γ} → s ↝ t → Term σ Γ
src {s = src} _ = src

tgt : ∀ {σ Γ} {s t : Term σ Γ} → s ↝ t → Term σ Γ
tgt {t = tgt} _ = tgt

_↝⋆_ : ∀ {σ} → [ Term σ ⟶ Term σ ⟶ κ Set ]
_↝⋆_ = Star _↝_

-- Stability of Reduction under thinning and substitution

th^↝ : ∀ {σ Γ Δ} {t u : Term σ Γ} (ρ : Thinning Γ Δ) → t ↝ u → ren ρ t ↝ ren ρ u
th^↝ ρ (β t u)    = subst (ren ρ (`λ t `∙ u) ↝_) (sym $ renβ TermD t u ρ) (β _ _)
th^↝ ρ ([λ] r)    = [λ] (th^↝ _ r)
th^↝ ρ ([∙]₁ f r) = [∙]₁ (ren ρ f) (th^↝ ρ r)
th^↝ ρ ([∙]₂ r t) = [∙]₂ (th^↝ ρ r) (ren ρ t)

-- Lemma 0.1
sub^↝ : ∀ {σ Γ Δ} {t u : Term σ Γ} (ρ : (Γ ─Env) Term Δ) → t ↝ u → sub ρ t ↝ sub ρ u
sub^↝ ρ (β t u)    = subst (sub ρ (`λ t `∙ u) ↝_) (sym $ subβ TermD t u ρ) (β (sub _ t) (sub ρ u))
sub^↝ ρ ([λ] r)    = [λ] (sub^↝ _ r)
sub^↝ ρ ([∙]₁ f r) = [∙]₁ (sub ρ f) (sub^↝ ρ r)
sub^↝ ρ ([∙]₂ r t) = [∙]₂ (sub^↝ ρ r) (sub ρ t)

[v↦t↝⋆t] : ∀ {Γ Δ} {ρ : (Γ ─Env) Term Δ} → rel.∀[ mkRel _↝⋆_ ] ρ ρ
lookup^R [v↦t↝⋆t] k = S.ε

sub^↝⋆ : ∀ {σ Γ Δ} (t : Term σ Γ) {ρ ρ′ : (Γ ─Env) Term Δ} →
         rel.∀[ mkRel _↝⋆_ ] ρ ρ′ → sub ρ t ↝⋆ sub ρ′ t
sub^↝⋆ t ρ^R = Sim.sim sim ρ^R t where

  sim : Sim (mkRel _↝⋆_) (mkRel _↝⋆_) TermD Substitution Substitution
  Sim.th^R  sim = λ ρ → S.gmap _ (th^↝ ρ)
  Sim.var^R sim = id
  Sim.alg^R sim = λ where
    (f `∙' t) {ρ₁} {ρ₂} ρ^R (refl , f^R , t^R , _) → S.gmap _ (λ f → [∙]₂ f (sub ρ₁ t)) f^R
                                                S.◅◅ S.gmap _ ([∙]₁ (sub ρ₂ f)) t^R
    (`λ' b) ρ^R (refl , b^R , _) → S.gmap `λ [λ] (b^R _ [v↦t↝⋆t])

-- Inversion lemmas for the interaction between ren, ∙, λ and ↝

ren⁻¹-∙ : ∀ {σ τ Γ Δ} (u : Term τ Γ) {f : Term (σ ⇒ τ) Δ} {t : Term σ Δ} (ρ : Thinning Γ Δ) →
          f `∙ t ≡ ren ρ u → ∃ λ f′ → ∃ λ t′ → f′ `∙ t′ ≡ u × f ≡ ren ρ f′ × t ≡ ren ρ t′
ren⁻¹-∙ (`var _)   ρ ()
ren⁻¹-∙ (`λ _)     ρ ()
ren⁻¹-∙ (f′ `∙ t′) ρ refl = f′ , t′ , refl , refl , refl

ren⁻¹-λ : ∀ {σ τ Γ Δ} (u : Term (σ ⇒ τ) Γ) {b : Term τ (σ ∷ Δ)} (ρ : Thinning Γ Δ) →
               `λ b ≡ ren ρ u → ∃ λ b′ → `λ b′ ≡ u × b ≡ ren (lift vl^Var (σ ∷ []) ρ) b′
ren⁻¹-λ (`var _) ρ ()
ren⁻¹-λ (_ `∙ _) ρ ()
ren⁻¹-λ (`λ b′)  ρ refl = b′ , refl , refl

th^↝-invert :  ∀ {σ Γ Δ} (t′ : Term σ Γ) {u : Term σ Δ} (ρ : Thinning Γ Δ) →
                ren ρ t′ ↝ u → ∃ λ u′ → u ≡ ren ρ u′ × t′ ↝ u′
th^↝-invert (`var v) ρ ()
th^↝-invert (`λ b `∙ t) ρ (β _ _) = b [ t /0] , sym (renβ TermD b t ρ) , β b t
th^↝-invert (`λ t)      ρ ([λ] r) =
  let (t′ , eq , r′) = th^↝-invert t _ r in `λ t′ , cong `λ eq , [λ] r′
th^↝-invert (f `∙ t) ρ ([∙]₁ ._ r) =
  let (t′ , eq , r′) = th^↝-invert t ρ r in f `∙ t′ , cong (ren ρ f `∙_) eq , [∙]₁ _ r′
th^↝-invert (f `∙ t) ρ ([∙]₂ r ._) =
  let (f′ , eq , r′) = th^↝-invert f ρ r in f′ `∙ t , cong (_`∙ ren ρ t) eq , [∙]₂ r′ _


-- Section 3 Defining Strongly Normalizing Terms
-------------------------------------------------------------------

-- Section 3.1 Definition of Strong Normalization via Accessibility Relation
-- Inductive definition of Strong Normalisation as the least set of
-- terms closed under reduction

Closed : (∀ {σ} → [ Term σ ⟶ Term σ ⟶ κ Set ]) →
         ∀ {σ Γ} → (Term σ Γ → Set) → Term σ Γ → Set
Closed red R t = ∀ {u} → red t u → R u

-- Definition 3.1
infix 3 _⊢sn_∋_
data _⊢sn_∋_ Γ σ (t : Term σ Γ) : Set where
  sn : Closed _↝_ (Γ ⊢sn σ ∋_) t → Γ ⊢sn σ ∋ t

Closed-SN : ∀ {σ Γ t} → Γ ⊢sn σ ∋ t → Closed _↝_ (Γ ⊢sn σ ∋_) t
Closed-SN (sn t^SN) = t^SN

-- Lemma 3.1
th^SN : ∀ {σ Γ Δ} ρ {t} → Γ ⊢sn σ ∋ t → Δ ⊢sn σ ∋ (ren ρ t)
th^SN ρ (sn u^SN) = sn $ λ r →
  let (_ , eq , r′) = th^↝-invert _ ρ r
  in subst (_ ⊢sn _ ∋_) (sym eq) $ th^SN ρ (u^SN r′)

-- Lemma 3.2
-- We start by an inductive definition of terms which are neutral
data WHNE {σ Γ} : Term σ Γ → Set where
  var : ∀ v → WHNE (`var v)
  app : ∀ {τ} {f : Term (τ ⇒ σ) Γ} → WHNE f → ∀ t → WHNE (f `∙ t)

WHNE^↝ : ∀ {σ Γ} {t u : Term σ Γ} → WHNE t → t ↝ u → WHNE u
WHNE^↝ (app f^WHNE _)  ([∙]₁ f r) = app f^WHNE _
WHNE^↝ (app f^WHNE _)  ([∙]₂ r t) = app (WHNE^↝ f^WHNE r) t
WHNE^↝ p               (β t u)    = case p of λ { (app () _) }

-- 1.
SN^WHNE∙ : ∀ {σ τ Γ f t} → WHNE f → Γ ⊢sn σ ⇒ τ ∋ f → Γ ⊢sn σ ∋ t → Γ ⊢sn τ ∋ f `∙ t
Closed-SN^WHNE∙ : ∀ {σ τ Γ f t} → WHNE f → Γ ⊢sn σ ⇒ τ ∋ f → Γ ⊢sn σ ∋ t → Closed _↝_ (Γ ⊢sn τ ∋_) (f `∙ t)

Closed-SN^WHNE∙ ()     f^SN      t^SN      (β t u)
Closed-SN^WHNE∙ f^whne f^SN      (sn t^SN) ([∙]₁ f r) = SN^WHNE∙ f^whne f^SN (t^SN r)
Closed-SN^WHNE∙ f^whne (sn f^SN) t^SN      ([∙]₂ r t) = SN^WHNE∙ (WHNE^↝ f^whne r) (f^SN r) t^SN

SN^WHNE∙ f^whne f^SN t^SN = sn (Closed-SN^WHNE∙ f^whne f^SN t^SN)

-- 2.
SN^sub⁻¹ : ∀ {σ Γ Δ} t ρ → Δ ⊢sn σ ∋ (sub ρ t) → Γ ⊢sn σ ∋ t
SN^sub⁻¹ t ρ (sn tρ^SN) = sn (λ r → SN^sub⁻¹ _ ρ (tρ^SN (sub^↝ ρ r)))

SN^[/0]⁻¹ : ∀ {σ τ Γ} t u → Γ ⊢sn τ ∋ (t [ u /0]) → (σ ∷ Γ) ⊢sn τ ∋ t
SN^[/0]⁻¹ t u t[u]^SN = SN^sub⁻¹ t (base vl^Tm ∙ u) t[u]^SN

-- 3.
SN-`λ : ∀ {σ τ Γ t} → (σ ∷ Γ) ⊢sn τ ∋ t → Γ ⊢sn σ ⇒ τ ∋ `λ t
SN-`λ (sn t^R) = sn λ { ([λ] r) → SN-`λ (t^R r) }

-- 4.
SN-`∙⁻¹ : ∀ {σ τ Γ f t} → Γ ⊢sn τ ∋ (f `∙ t) → Γ ⊢sn σ ⇒ τ ∋ f × Γ ⊢sn σ ∋ t
SN-`∙⁻¹ (sn ft^SN) = sn (λ r → proj₁ (SN-`∙⁻¹ (ft^SN ([∙]₂ r _))))
                   , sn (λ r → proj₂ (SN-`∙⁻¹ (ft^SN ([∙]₁ _ r))))

-- 5.
SN-`λ⁻¹ : ∀ {σ τ Γ t} → Γ ⊢sn σ ⇒ τ ∋ `λ t → (σ ∷ Γ) ⊢sn τ ∋ t
SN-`λ⁻¹ (sn λt^SN) = sn (λ r → SN-`λ⁻¹ (λt^SN ([λ] r)))

-- Evaluation contexts indexed by the Scope, the type of the hole, and the
-- type of the overall expression. Not sure whether they should be presented
-- inside-out or outside-in so we define both for the moment.

infix 3 _⊢C<_>∈_ _⊢_∋C<_>
data _⊢C<_>∈_ Γ α : Type → Set where
  <>  : Γ ⊢C< α >∈ α
  app : ∀ {σ τ} → Γ ⊢C< α >∈ σ ⇒ τ → Term σ Γ → Γ ⊢C< α >∈ τ

data _⊢_∋C<_> Γ α : Type → Set where
  <>  : Γ ⊢ α ∋C< α >
  app : ∀ {σ τ} → Γ ⊢ α ∋C< τ > → Term σ Γ → Γ ⊢ α ∋C< σ ⇒ τ >

plug^∈ : ∀ {Γ α σ} → Term α Γ → Γ ⊢C< α >∈ σ → Term σ Γ
plug^∈ t <>        = t
plug^∈ t (app c u) = plug^∈ t c `∙ u

plug^∋ : ∀ {Γ α σ} → Term σ Γ → Γ ⊢ α ∋C< σ > → Term α Γ
plug^∋ t <>        = t
plug^∋ t (app c u) = plug^∋ (t `∙ u) c


{-
unzip : ∀ {Γ σ τ} (f : Term (σ ⇒ τ) Γ) t → ∃ λ α → ∃ λ (c : C[] Γ α τ) →
        (∃ λ v → plug (`var v) c ≡ f `∙ t)
        ⊎ (∃ λ β → ∃ λ (b : Term α (β ∷ Γ)) → ∃ λ u → plug (`λ b `∙ u) c ≡ f `∙ t)
unzip (`var v) t = _ , app [] t , inj₁ (v , refl)
unzip (`λ b)   t = _ , [] , inj₂ (_ , b , t , refl)
unzip (f `∙ u) t with unzip f u
... | (_ , c , inj₁ (v , eq))          = _ , app c t , inj₁ (v , cong (_`∙ t) eq)
... | (_ , c , inj₂ (_ , b , u′ , eq)) = _ , app c t , inj₂ (_ , b , u′ , cong (_`∙ t) eq)
-}

C[v]^WHNE : ∀ {Γ α σ v} (c : Γ ⊢C< α >∈ σ) → WHNE (plug^∈ (`var v) c)
C[v]^WHNE <>        = var _
C[v]^WHNE (app c t) = app (C[v]^WHNE c) t

WHNE^C[v] : ∀ {Γ σ} {t : Term σ Γ} → WHNE t →
            ∃ λ α → ∃ λ c → ∃ λ (v : Var α Γ) → t ≡ plug^∈ (`var v) c
WHNE^C[v] (var v)        = _ , <> , v , refl
WHNE^C[v] (app t^WHNE t) =
  let (_ , c , v , eq) = WHNE^C[v] t^WHNE in _ , app c t , v , cong (_`∙ t) eq

-- Lemma 3.3
plugvar^↝⁻¹ : ∀ {Γ α σ v} (c : Γ ⊢C< α >∈ σ) {u} → plug^∈ (`var v) c ↝ u →
              ∃ λ c′ → u ≡ plug^∈ (`var v) c′
plugvar^↝⁻¹ (app <> t)          ([∙]₁ _ r)  = app <> _ , refl
plugvar^↝⁻¹ (app c@(app _ _) t) ([∙]₁ _ r)  = app c _ , refl
plugvar^↝⁻¹ (app c@(app _ _) t) ([∙]₂ r .t) =
  let (c′ , r′) = plugvar^↝⁻¹ c r in app c′ _ , cong (_`∙ _) r′
plugvar^↝⁻¹ (app <> t)          ([∙]₂ () .t)
plugvar^↝⁻¹ <>                  ()

-- Lemma 3.4
-- 1.
SN-`var : ∀ {σ Γ} → (v : Var σ Γ) → Γ ⊢sn σ ∋ (`var v)
SN-`var v = sn (λ ())

-- 2. (By Lemma 3.2-1)
SN-C[var]∙ : ∀ {Γ α σ τ v t} (c : Γ ⊢C< α >∈ σ ⇒ τ) → Γ ⊢sn σ ⇒ τ ∋ plug^∈ (`var v) c → Γ ⊢sn σ ∋ t → Γ ⊢sn τ ∋ (plug^∈ (`var v) (app c t))
SN-C[var]∙ c c[v]^SN t^SN = SN^WHNE∙ (C[v]^WHNE c) c[v]^SN t^SN

-- 3.
SN-C[var]∙^↝ : ∀ {Γ α σ τ v t u} (c : Γ ⊢C< α >∈ σ ⇒ τ) →
  plug^∈ (`var v) (app c t) ↝ u → Γ ⊢sn σ ⇒ τ ∋ plug^∈ (`var v) c → Γ ⊢sn σ ∋ t → Γ ⊢sn τ ∋ u
SN-C[var]∙^↝ <>        ([∙]₁ _ r)  c[v]^SN t^SN = SN^WHNE∙ (var _) c[v]^SN (Closed-SN t^SN r)
SN-C[var]∙^↝ <>        ([∙]₂ () t) c[v]^SN t^SN
SN-C[var]∙^↝ (app c u) ([∙]₁ _ r)  c[v]^SN t^SN = SN^WHNE∙ (app (C[v]^WHNE c) _) c[v]^SN (Closed-SN t^SN r)
SN-C[var]∙^↝ (app c u) ([∙]₂ r t)  c[v]^SN t^SN =
  let (c′ , eq) = plugvar^↝⁻¹ (app c u) r in
  SN^WHNE∙ (subst WHNE (sym eq) (C[v]^WHNE c′)) (Closed-SN c[v]^SN r) t^SN

-- Section 3.2 Inductive Definition of Strongly Normalizing Terms

infix 5 _⊢SN_∋_<_ _⊢NE_∋_<_ _⊢SN_∋_ _⊢NE_∋_
data _⊢SN_∋_<_ (Γ : List Type) : (σ : Type) → Term σ Γ → Size → Set
data _⊢NE_∋_<_ (Γ : List Type) : (σ : Type) → Term σ Γ → Size → Set

infix 3 _↝SN_<_ _↝SN_
data _↝SN_<_ : ∀ {σ} → [ Term σ ⟶ Term σ ⟶ κ Size ⟶ κ Set ] where
-- computational
  β    : ∀ {Γ σ τ i} (t : Term τ (σ ∷ Γ)) u → Γ ⊢SN σ ∋ u < i → `λ t `∙ u ↝SN t [ u /0] < ↑ i
-- structural
  [∙]₂ : ∀ {Γ σ τ i} {f g : Term (σ ⇒ τ) Γ} → f ↝SN g < i → ∀ t → f `∙ t ↝SN g `∙ t < ↑ i

data _⊢SN_∋_<_ Γ where
  neu : ∀ {σ t i} → Γ ⊢NE σ ∋ t < i → Γ ⊢SN σ ∋ t < ↑ i
  lam : ∀ {σ τ b i} → (σ ∷ Γ) ⊢SN τ ∋ b < i → Γ ⊢SN σ ⇒ τ ∋ `λ b < ↑ i
  red : ∀ {σ t t′ i} → t ↝SN t′ < i → Γ ⊢SN σ ∋ t′ < i → Γ ⊢SN σ ∋ t < ↑ i

data _⊢NE_∋_<_ Γ where
  var : ∀ {σ i} v → Γ ⊢NE σ ∋ `var v < ↑ i
  app : ∀ {σ τ f t i} → Γ ⊢NE σ ⇒ τ ∋ f < i → Γ ⊢SN σ ∋ t < i → Γ ⊢NE τ ∋ f `∙ t < ↑ i

-- Why isn't this trivially true?
wk^↝SN : ∀ {Γ σ i} {t u : Term σ Γ} → t ↝SN u < i → t ↝SN u < ↑ i
wk^SN∋ : ∀ {Γ σ t i} → Γ ⊢SN σ ∋ t < i → Γ ⊢SN σ ∋ t < ↑ i
wk^NE∋ : ∀ {Γ σ t i} → Γ ⊢NE σ ∋ t < i → Γ ⊢NE σ ∋ t < ↑ i

wk^↝SN (β t u u^SN)    = β t u (wk^SN∋ u^SN)
wk^↝SN ([∙]₂ r t)      = [∙]₂ (wk^↝SN r) t
wk^SN∋ (neu t^NE)      = neu (wk^NE∋ t^NE)
wk^SN∋ (lam b^SN)      = lam (wk^SN∋ b^SN)
wk^SN∋ (red r t^SN)    = red (wk^↝SN r) (wk^SN∋ t^SN)
wk^NE∋ (var v)         = var v
wk^NE∋ (app f^NE t^SN) = app (wk^NE∋ f^NE) (wk^SN∋ t^SN)

_↝SN_ : ∀ {σ} → [ Term σ ⟶ Term σ ⟶ κ Set ]
_↝SN_   = _↝SN_< _
_⊢SN_∋_ = _⊢SN_∋_< _
_⊢NE_∋_ = _⊢NE_∋_< _

SN^tm : ∀ {Γ σ t} → Γ ⊢SN σ ∋ t → Term σ Γ
SN^tm {t = t} _ = t

NE^WHNE : ∀ {Γ σ t} → Γ ⊢NE σ ∋ t → WHNE t
NE^WHNE (var v)      = var v
NE^WHNE (app f^NE _) = app (NE^WHNE f^NE) _

SN∋-`λ⁻¹ : ∀ {Γ σ τ b} → Γ ⊢SN σ ⇒ τ ∋ `λ b → (σ ∷ Γ) ⊢SN τ ∋ b
SN∋-`λ⁻¹ (lam b) = b
SN∋-`λ⁻¹ (red () _)
SN∋-`λ⁻¹ (neu ())

C<>∈^↝SN : ∀ {Γ α σ t u} (c : Γ ⊢C< α >∈ σ) → t ↝SN u → plug^∈ t c ↝SN plug^∈ u c
C<>∈^↝SN <>        r = r
C<>∈^↝SN (app c t) r = [∙]₂ (C<>∈^↝SN c r) t

C<>∈^↝ : ∀ {Γ α σ t u} (c : Γ ⊢C< α >∈ σ) → t ↝ u → plug^∈ t c ↝ plug^∈ u c
C<>∈^↝ <>        r = r
C<>∈^↝ (app c t) r = [∙]₂ (C<>∈^↝ c r) t

C<>∈^↝⋆ : ∀ {Γ α σ t u} (c : Γ ⊢C< α >∈ σ) → t ↝⋆ u → plug^∈ t c ↝⋆ plug^∈ u c
C<>∈^↝⋆ c = S.gmap (flip plug^∈ c) (C<>∈^↝ c)

∋C<>^↝SN : ∀ {Γ α σ t u} (c : Γ ⊢ α ∋C< σ >) → t ↝SN u → plug^∋ t c ↝SN plug^∋ u c
∋C<>^↝SN <>        r = r
∋C<>^↝SN (app c t) r = ∋C<>^↝SN c ([∙]₂ r t)

∋C<>^↝ : ∀ {Γ α σ t u} (c : Γ ⊢ α ∋C< σ >) → t ↝ u → plug^∋ t c ↝ plug^∋ u c
∋C<>^↝ <>        r = r
∋C<>^↝ (app c t) r = ∋C<>^↝ c ([∙]₂ r t)

∋C<>^↝⋆ : ∀ {Γ α σ t u} (c : Γ ⊢ α ∋C< σ >) → t ↝⋆ u → plug^∋ t c ↝⋆ plug^∋ u c
∋C<>^↝⋆ c = S.gmap (flip plug^∋ c) (∋C<>^↝ c)

SN∋ : Pred Term
pred SN∋ = _ ⊢SN _ ∋_

NE∋ : Pred Term
pred NE∋ = _ ⊢NE _ ∋_

[v↦v]^NE : ∀ {Γ} → pred.∀[ NE∋ ] (base vl^Tm {Γ})
lookup^P [v↦v]^NE v rewrite lookup-base^Tm {d = TermD} v = var v

-- Lemma 3.6: Neutral and Normal Thinning
mutual

 -- 1.
 th^SN∋ : ∀ {σ Γ Δ t} ρ → Γ ⊢SN σ ∋ t → Δ ⊢SN σ ∋ ren ρ t
 th^SN∋ ρ (neu n)   = neu (th^NE∋ ρ n)
 th^SN∋ ρ (lam t)   = lam (th^SN∋ _ t)
 th^SN∋ ρ (red r t) = red (th^↝SN ρ r) (th^SN∋ ρ t)

 -- 2.
 th^NE∋ : ∀ {σ Γ Δ t} ρ → Γ ⊢NE σ ∋ t → Δ ⊢NE σ ∋ ren ρ t
 th^NE∋ ρ (var v)   = var (lookup ρ v)
 th^NE∋ ρ (app n t) = app (th^NE∋ ρ n) (th^SN∋ ρ t)

 -- 3.
 th^↝SN : ∀ {σ Γ Δ} {t u : Term σ Γ} (ρ : Thinning Γ Δ) → t ↝SN u → ren ρ t ↝SN ren ρ u
 th^↝SN ρ (β t u u^SN) = subst (ren ρ (`λ t `∙ u) ↝SN_< _) (sym $ renβ TermD t u ρ)
                       $ β _ (ren ρ u) (th^SN∋ ρ u^SN)
 th^↝SN ρ ([∙]₂ r t)   = [∙]₂ (th^↝SN ρ r) (ren ρ t)

-- Lemma 3.7: Neutral and Normal anti-Thinning
mutual

 -- 1.
 th⁻¹^SN∋ : ∀ {σ Γ Δ t′} t ρ → t′ ≡ ren ρ t → Δ ⊢SN σ ∋ t′ → Γ ⊢SN σ ∋ t
 th⁻¹^SN∋ (`var v) ρ refl (red r pr) =
   let (v′ , eq , r′) = th⁻¹^↝SN∋ (`var v) ρ r
   in red r′ (th⁻¹^SN∋ v′ ρ eq pr)
 th⁻¹^SN∋ (f `∙ t) ρ refl (red r pr) =
   let (ft′ , eq , r′) = th⁻¹^↝SN∋ (f `∙ t) ρ r
   in red r′ (th⁻¹^SN∋ ft′ ρ eq pr)
 th⁻¹^SN∋ (`λ t)   ρ refl (red r pr) =
   let (λt′ , eq , r′) = th⁻¹^↝SN∋ (`λ t) ρ r
   in red r′ (th⁻¹^SN∋ λt′ ρ eq pr)
 th⁻¹^SN∋ (`var v) ρ eq   (neu pr) = neu (th⁻¹^NE∋ _ ρ eq pr)
 th⁻¹^SN∋ (f `∙ t) ρ eq   (neu pr) = neu (th⁻¹^NE∋ _ ρ eq pr)
 th⁻¹^SN∋ (`λ t)   ρ refl (lam pr) = lam (th⁻¹^SN∋ t _ refl pr)
 th⁻¹^SN∋ (`λ t)   ρ refl (neu ())

 -- 2.
 th⁻¹^NE∋ : ∀ {σ Γ Δ t′} t ρ → t′ ≡ ren ρ t → Δ ⊢NE σ ∋ t′ → Γ ⊢NE σ ∋ t
 th⁻¹^NE∋ (`var v) ρ refl (var _)     = var v
 th⁻¹^NE∋ (f `∙ t) ρ refl (app rf rt) =
  app (th⁻¹^NE∋ f ρ refl rf) (th⁻¹^SN∋ t ρ refl rt)

 -- 3.
 th⁻¹^↝SN∋ : ∀ {σ Γ Δ} (t : Term σ Γ) {u : Term σ Δ} ρ →
             ren ρ t ↝SN u → ∃ λ u′ → u ≡ ren ρ u′ × t ↝SN u′
 th⁻¹^↝SN∋ (`var v) ρ ()
 th⁻¹^↝SN∋ (`λ b)   ρ ()
 th⁻¹^↝SN∋ (`λ b `∙ t) ρ (β ._ ._ t^SN) = b [ t /0] , sym (renβ TermD b t ρ) , β b t (th⁻¹^SN∋ t ρ refl t^SN)
 th⁻¹^↝SN∋ (f `∙ t)    ρ ([∙]₂ r ._)    =
   let (g , eq , r′) = th⁻¹^↝SN∋ f ρ r in g `∙ t , cong (_`∙ ren ρ t) eq , [∙]₂ r′ t

-- Lemma 3.8: Stability under substitution of Strongly Neutrals
mutual

 -- 1.
 sub^SN∋ : ∀ {σ Γ Δ t ρ} → pred.∀[ NE∋ ] ρ → Γ ⊢SN σ ∋ t → Δ ⊢SN σ ∋ sub ρ t
 sub^SN∋ ρ^P (neu n)   = neu (sub^NE∋ ρ^P n)
 sub^SN∋ ρ^P (lam t)   = lam (sub^SN∋ ρ′^P t) where
   ρ′^P = pack^P $ λ where
     z     → var z
     (s k) → th^NE∋ _ (lookup^P ρ^P k)
 sub^SN∋ ρ^P (red r t) = red (sub^↝SN ρ^P r) (sub^SN∋ ρ^P t)

 -- 2.
 sub^NE∋ : ∀ {σ Γ Δ t ρ} → pred.∀[ NE∋ ] ρ → Γ ⊢NE σ ∋ t → Δ ⊢NE σ ∋ sub ρ t
 sub^NE∋ ρ^P (var v)   = lookup^P ρ^P v
 sub^NE∋ ρ^P (app n t) = app (sub^NE∋ ρ^P n) (sub^SN∋ ρ^P t)

 -- 3.
 sub^↝SN : ∀ {σ Γ Δ} {t u : Term σ Γ} {ρ : (Γ ─Env) Term Δ} → pred.∀[ NE∋ ] ρ → t ↝SN u → sub ρ t ↝SN sub ρ u
 sub^↝SN ρ^P (β t u u^SN) = subst (sub _ (`λ t `∙ u) ↝SN_) (sym $ subβ TermD t u _)
                        $ β (sub _ t) (sub _ u) (sub^SN∋ ρ^P u^SN)
 sub^↝SN ρ^P ([∙]₂ r t)   = [∙]₂ (sub^↝SN ρ^P r) (sub _ t)

-- Lemma 3.9: Stability under application to a strongly neutral
infixl 5 _∙SN_
_∙SN_ : ∀ {Γ σ τ f t} → Γ ⊢SN σ ⇒ τ ∋ f → Γ ⊢NE σ ∋ t → Γ ⊢SN τ ∋ f `∙ t
neu f^NE   ∙SN t^NE = neu (app f^NE (neu t^NE))
lam b^SN   ∙SN t^NE = red (β _ _ (neu t^NE)) (sub^SN∋ ([v↦v]^NE ∙^P t^NE) b^SN)
red r f^SN ∙SN t^NE = red ([∙]₂ r _) (f^SN ∙SN t^NE)

-- Lemma 3.10: Stability under application to a variable
infixl 5 _∙SNvar_
_∙SNvar_ : ∀ {Γ σ τ f} → Γ ⊢SN σ ⇒ τ ∋ f → (v : Var σ Γ) → Γ ⊢SN τ ∋ f `∙ `var v
f^SN ∙SNvar v = f^SN ∙SN var v

-- Lemma 3.11: Extensionality of SN
NE∋-ext : ∀ {Γ σ τ f} v → Γ ⊢NE τ ∋ f `∙ `var v → Γ ⊢NE σ ⇒ τ ∋ f
NE∋-ext v (app f^NE v^SN) = f^NE

SN∋-ext : ∀ {Γ σ τ f} v → Γ ⊢SN τ ∋ f `∙ `var v → Γ ⊢SN σ ⇒ τ ∋ f
SN∋-ext v (neu fv^NE)   = neu (NE∋-ext v fv^NE)
SN∋-ext v (red ([∙]₂ r .(`var v))   fv^SN) = red r (SN∋-ext v fv^SN)
SN∋-ext v (red (β t .(`var v) v^SN) fv^SN) = lam (th⁻¹^SN∋ t (base vl^Var ∙ v) eq fv^SN) where
  eq = sym $ Sim.sim sim.RenSub (base^VarTm^R ∙^R refl) t


-- Lemma [APLAS]: confluence of ↝SN and ↝ together with
-- stability of SN∋ and NE∋ under ↝ reduction
mutual

 ↜-↝^SN-confl : ∀ {Γ σ i} {t u u′ : Term σ Γ} → t ↝ u → t ↝SN u′ < i →
                u ≡ u′ ⊎ ∃ λ t′ → u ↝SN t′ < i × u′ ↝⋆ t′
 ↜-↝^SN-confl (β b t) (β .b .t t^SN) = inj₁ refl
 ↜-↝^SN-confl ([∙]₂ ([λ] r) t) (β b .t t^SN) =
   inj₂ (tgt r [ t /0] , β (tgt r) t t^SN , S.return (sub^↝ (t /0]) r))
 ↜-↝^SN-confl ([∙]₁ f r) (β b t t^SN) =
   inj₂ (b [ tgt r /0] , β b (tgt r) (↝^SN∋ t^SN r) , sub^↝⋆ b ([v↦t↝⋆t] ∙^R S.return r))
 ↜-↝^SN-confl (β b t) ([∙]₂ () .t)
 ↜-↝^SN-confl ([∙]₁ f r) ([∙]₂ r^SN t) =
   inj₂ (_ , [∙]₂ r^SN _ , S.return ([∙]₁ _ r))
 ↜-↝^SN-confl ([∙]₂ r t) ([∙]₂ r^SN .t) with ↜-↝^SN-confl r r^SN
 ... | inj₁ eq = inj₁ (cong (_`∙ t) eq)
 ... | inj₂ (f , r′ , r′^SN) =
   inj₂ (f `∙ t , [∙]₂ r′ t , S.gmap (_`∙ t) (λ r → [∙]₂ r t) r′^SN)

 ↝^SN∋ : ∀ {Γ σ t u i} → Γ ⊢SN σ ∋ t < i → t ↝ u → Γ ⊢SN σ ∋ u < i
 ↝^SN∋ (neu t^NE)    r       = neu (↝^NE∋ t^NE r)
 ↝^SN∋ (lam b^SN)    ([λ] r) = lam (↝^SN∋ b^SN r)
 ↝^SN∋ (red rt t^SN) r       with ↜-↝^SN-confl r rt
 ... | inj₁ eq rewrite eq = wk^SN∋ t^SN
 ... | inj₂ (t′ , rt′ , rs) = red rt′ (↝⋆^SN∋ t^SN rs)

 ↝^NE∋ : ∀ {Γ σ t u i} → Γ ⊢NE σ ∋ t < i → t ↝ u → Γ ⊢NE σ ∋ u < i
 ↝^NE∋ (var v) ()
 ↝^NE∋ (app () t^SN) (β t u)
 ↝^NE∋ (app f^NE t^SN) ([∙]₁ f r) = app f^NE (↝^SN∋ t^SN r)
 ↝^NE∋ (app f^NE t^SN) ([∙]₂ r t) = app (↝^NE∋ f^NE r) t^SN

 ↝⋆^SN∋ : ∀ {Γ σ t u i} → Γ ⊢SN σ ∋ t < i → t ↝⋆ u → Γ ⊢SN σ ∋ u < i
 ↝⋆^SN∋ t^SN Star.ε        = t^SN
 ↝⋆^SN∋ t^SN (r Star.◅ rs) = ↝⋆^SN∋ (↝^SN∋ t^SN r) rs

-- Section 3.3 Soundness and Completeness

-- Theorem 3.13 Soundness of SN
mutual

 -- 1.
  sound^SN∋ : ∀ {Γ σ t} → Γ ⊢SN σ ∋ t → Γ ⊢sn σ ∋ t
  sound^SN∋ (neu t^NE)   = sound^NE∋ t^NE
  sound^SN∋ (lam b^SN)   = SN-`λ (sound^SN∋ b^SN)
  sound^SN∋ (red r t^SN) = sn (sound^↝SN <> r t^SN (sound^SN∋ t^SN))

  -- 2.
  sound^NE∋ : ∀ {Γ σ t} → Γ ⊢NE σ ∋ t → Γ ⊢sn σ ∋ t
  sound^NE∋ (var v)         = SN-`var v
  sound^NE∋ (app f^NE t^SN) = SN^WHNE∙ (NE^WHNE f^NE) (sound^NE∋ f^NE) (sound^SN∋ t^SN)

  -- 3.
  sound^↝SN : ∀ {Γ α σ t u t′} (c : Γ ⊢ σ ∋C< α >) →
              t ↝SN u → Γ ⊢SN σ ∋ plug^∋ u c → Γ ⊢sn σ ∋ (plug^∋ u c) → t ↝ t′ → Γ ⊢sn σ ∋ (plug^∋ t′ c)
  sound^↝SN c (β b u u^SN) ^SN∋ ^SN (β .b .u)        = ^SN
  sound^↝SN c (β b u u^SN) ^SN∋ ^SN ([∙]₁ .(`λ b) r) = {!!}
  sound^↝SN c (β b u u^SN) ^SN∋ ^SN ([∙]₂ r .u)      = {!!}

  sound^↝SN c ([∙]₂ () .u)  ^SN∋ ^SN (β b u)
  sound^↝SN c ([∙]₂ r^SN t) ^SN∋ (sn ^SN) ([∙]₁ f r) =
    let ^SN∋′ = ↝^SN∋ ^SN∋ (∋C<>^↝ c ([∙]₁ _ r)) in
    let ^SN′  = ^SN (∋C<>^↝ c ([∙]₁ _ r)) in
    sn (sound^↝SN <> (∋C<>^↝SN c ([∙]₂ r^SN _)) ^SN∋′ ^SN′)
  sound^↝SN c ([∙]₂ r^SN t) ^SN∋ ^SN ([∙]₂ r .t) = sound^↝SN (app c t) r^SN ^SN∋ ^SN r


-- Theorem 3.14 Completeness of SN
-- We start with a definition of deeply nested β-redexes

data RED {Γ σ} : Term σ Γ → Set where
  β   : ∀ {τ} b (u : Term τ Γ) → RED (`λ b `∙ u)
  app : ∀ {τ f} → RED f → ∀ (t : Term τ Γ) → RED (f `∙ t)

WHNE+RED : ∀ {Γ σ τ} (f : Term (σ ⇒ τ) Γ) t → WHNE (f `∙ t) ⊎ RED (f `∙ t)
WHNE+RED (`var v) t = inj₁ (app (var v) t)
WHNE+RED (`λ b)   t = inj₂ (β b t)
WHNE+RED (f `∙ u) t = Sum.map (λ whn → app whn t) (λ rdx → app rdx t) (WHNE+RED f u)

C[β]^RED : ∀ {Γ α σ τ b} {t : Term τ Γ} (c : Γ ⊢C< α >∈ σ) → RED (plug^∈ (`λ b `∙ t) c)
C[β]^RED <>        = β _ _
C[β]^RED (app c t) = app (C[β]^RED c) t

-- We use these reformulated versions for the proof because they
-- make the recursion obviously structural
mutual

  -- 1.
  complete^SN-WHNE : ∀ {Γ σ t} → WHNE t → Γ ⊢sn σ ∋ t → Γ ⊢NE σ ∋ t
  complete^SN-WHNE (var v)        e^SN = var v
  complete^SN-WHNE (app f^WHNE t) e^SN =
    let (f^SN , t^SN) = SN-`∙⁻¹ e^SN in
    app (complete^SN-WHNE f^WHNE f^SN) (complete^SN t t^SN)

  -- 2.
  complete^SN-RED : ∀ {Γ σ t} → RED t → Γ ⊢sn σ ∋ t → Γ ⊢SN σ ∋ t
  complete^SN-RED (β b u)       λbu^SN =
    let (λb^SN , u^SN) = SN-`∙⁻¹ λbu^SN in
    red (β b u (complete^SN u u^SN)) {!!}
--    red (β b u) (sub^SN∋ ([v↦v]^SN ∙^P complete^SN _ u^SN) (SN∋-`λ⁻¹ (complete^SN _ λb^SN)))
  complete^SN-RED (app f^RED t) ft^SN  =
    let (f^SN , t^SN) = SN-`∙⁻¹ ft^SN in
    {!!} -- complete^SN-RED f^RED f^SN ∙SN complete^SN t t^SN

  -- 3.
  complete^SN : ∀ {Γ σ} t → Γ ⊢sn σ ∋ t → Γ ⊢SN σ ∋ t
  complete^SN (`var v) v^SN  = neu (var v)
  complete^SN (`λ b)   λb^SN = lam (complete^SN b (SN-`λ⁻¹ λb^SN))
  complete^SN (f `∙ t) ft^SN with WHNE+RED f t
  ... | inj₁ ft^WHNE = neu (complete^SN-WHNE ft^WHNE ft^SN)
  ... | inj₂ ft^RED  = complete^SN-RED ft^RED ft^SN


complete^SN-C[v] : ∀ {Γ α σ v} (c : Γ ⊢C< α >∈ σ) → let t = plug^∈ (`var v) c in Γ ⊢sn σ ∋ t → Γ ⊢NE σ ∋ t
complete^SN-C[v] c = complete^SN-WHNE (C[v]^WHNE c)

complete^SN-c[β] : ∀ {Γ α σ τ t} {b : Term τ (σ ∷ Γ)} c → Γ ⊢sn α ∋ plug^∈ ((`λ b) `∙ t) c →
                   Γ ⊢SN α ∋ plug^∈ (`λ b `∙ t) c
complete^SN-c[β] c = complete^SN-RED (C[β]^RED c)


-- Section 4 Reducibility Candidates
-------------------------------------------------------------------


{-
𝓡' : Pred Term
𝓡  : ∀ {σ} → [ Term σ ⟶ κ Set ]

pred 𝓡' {α}         t = SN t
pred 𝓡' {σ ⇒ τ} {Γ} t = ∀ {Δ} (ρ : Thinning Γ Δ) {u} → 𝓡 u → 𝓡 (ren ρ t `∙ u)

𝓡 = pred 𝓡'



lemma2-1 : ∀ {σ τ Γ} {t : Term (σ ⇒ τ) Γ} {u : Term σ Γ} → 𝓡 t → 𝓡 u → 𝓡 (t `∙ u)
lemma2-1 {t = t} T U = subst (λ t → 𝓡 (t `∙ _)) (ren-id t) (T (base vl^Var) U)


lemma2-3 : ∀ σ {Γ Δ} (ρ : Thinning Γ Δ) (t : Term σ Γ) → 𝓡 t → 𝓡 (ren ρ t)
lemma2-3 α       ρ t T = th^SN ρ T
lemma2-3 (σ ⇒ τ) ρ t T = λ ρ′ U → subst (λ t → 𝓡 (t `∙ _)) (sym (ren² TermD t ρ ρ′)) (T (select ρ ρ′) U)

ηexp : ∀ {σ τ} → [ Term (σ ⇒ τ) ⟶ Term (σ ⇒ τ) ]
ηexp t = `λ (ren extend t `∙ `var z)

ηexp^↝ : ∀ {σ τ Γ} {t u : Term (σ ⇒ τ) Γ} → t ↝ u → ηexp t ↝ ηexp u
ηexp^↝ r = [λ] ([∙]₂ (th^↝ extend r) (`var z))

SN-η : ∀ {σ τ Γ} {t : Term (σ ⇒ τ) Γ} → SN (ηexp t) → SN t
SN-η (sn pr) = sn (λ r → SN-η (pr (ηexp^↝ r)))

th^WHNE : ∀ {σ Γ Δ} (ρ : Thinning Γ Δ) {t : Term σ Γ} → WHNE t → WHNE (ren ρ t)
th^WHNE ρ (var v)        = var (lookup ρ v)
th^WHNE ρ (app f^WHNE t) = app (th^WHNE ρ f^WHNE) (ren ρ t)

Closed-𝓡 : ∀ σ {Γ} {t : Term σ Γ} → 𝓡 t → Closed _↝_ 𝓡 t
Closed-𝓡 α       t^R = Closed-SN t^R
Closed-𝓡 (σ ⇒ τ) t^R = λ r ρ u^R → Closed-𝓡 τ (t^R ρ u^R) ([∙]₂ (th^↝ ρ r) _)

Closed⋆-𝓡 : ∀ {σ Γ} {t : Term σ Γ} → 𝓡 t → Closed _↝⋆_ 𝓡 t
Closed⋆-𝓡 t^R Star.ε        = t^R
Closed⋆-𝓡 t^R (r Star.◅ rs) = Closed⋆-𝓡 (Closed-𝓡 _ t^R r) rs

𝓡⇒SN       : ∀ σ {Γ} (t : Term σ Γ) → 𝓡 t → SN t
NE⇒𝓡       : ∀ σ {Γ} (t : Term σ Γ) → WHNE t → Closed _↝_ 𝓡 t → 𝓡 t
Closed-𝓡-∙ : ∀ {σ τ Γ} {t : Term (σ ⇒ τ) Γ} → WHNE t → Closed _↝_ 𝓡 t →
              ∀ {a} → 𝓡 a → SN a → Closed _↝_ 𝓡 (t `∙ a)

𝓡⇒SN α       t t^R = t^R
𝓡⇒SN (σ ⇒ τ) t t^R = SN-η ηt where

  𝓡[t∙z] : 𝓡 (ren extend t `∙ `var z)
  𝓡[t∙z] = lemma2-1 (lemma2-3 (σ ⇒ τ) extend t t^R) (NE⇒𝓡 σ (`var z) (var z) (λ ()))

  ηt : SN (`λ (ren extend t `∙ `var z))
  ηt = SN-`λ (𝓡⇒SN τ (ren extend t `∙ `var z) 𝓡[t∙z])

NE⇒𝓡 α       t t^NE t^R           = sn t^R
NE⇒𝓡 (σ ⇒ τ) t t^NE t^R ρ {u} u^R = NE⇒𝓡 τ (ren ρ t `∙ u) (app (th^WHNE ρ t^NE) u) tρ∙u^R
  where u^SN   = 𝓡⇒SN σ _ u^R
        tρ^R   : Closed _↝_ 𝓡 (ren ρ t)
        tρ^R r = let (u′ , eq , r′) = th^↝-invert t ρ r
                 in subst 𝓡 (sym eq) (lemma2-3 (σ ⇒ τ) ρ u′ (t^R r′))
        tρ∙u^R : Closed _↝_ 𝓡 (ren ρ t `∙ u)
        tρ∙u^R = Closed-𝓡-∙ (th^WHNE ρ t^NE) tρ^R u^R u^SN

Closed-𝓡-∙ ()   t^R a^R a^SN      (β t u)
Closed-𝓡-∙ t^NE t^R a^R (sn a^SN) ([∙]₁ t r) =
  NE⇒𝓡 _ _ (app t^NE _) (Closed-𝓡-∙ t^NE t^R (Closed-𝓡 _ a^R r) (a^SN r))
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

𝓡-β t^SN u^SN tu^R = NE⇒𝓡 _ _ {!!} (Closed-𝓡-β t^SN u^SN tu^R)

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

-}
\end{code}

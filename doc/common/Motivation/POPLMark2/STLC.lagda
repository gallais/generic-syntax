\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Motivation.POPLMark2.STLC where

open import Data.Var hiding (_<$>_)
open import Data.Var.Varlike
open import Data.Environment
open import Data.Pred as P
open import Data.Relation as R
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Identity hiding (`con)
open import Generic.Fundamental as Fdm
open import Generic.Simulation
import Generic.Simulation.Syntactic as Sim
open import Generic.Fusion
open import Generic.Fusion.Syntactic

open import Size
open import Data.Sum as Sum
open import Data.Product as Prod
open import Agda.Builtin.List
open import Data.Product
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as S using (Star)
open import Function hiding (_∋_)
open import Relation.Binary.PropositionalEquality hiding ([_]); open ≡-Reasoning

-- Section 1 Simply-Typed Lambda Calculus with Type-directed Reduction

-- Definition of the language. We define an enumeration `TermC` as the
-- type of constructor instead of using Booleans. This allows us to have
-- a clearer definition as well as storing the needed type arguments in
-- the constructor itself rather than having to use multiple extra `σ
-- constructors in the Desc.

data Type : Set where
  α    : Type
  _⇒_  : Type → Type → Type

data TermC : Set where
  Lam  : Type → Type → TermC
  App  : Type → Type → TermC

TermD : Desc Type
TermD =  `σ TermC λ where
  (Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ ⇒ τ))
  (App σ τ) → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ))

Term : Type ─Scoped
Term = Tm TermD _


private
  variable
    σ τ ⊡ : Type
    Γ Δ : List Type
    t u u′ f g b b′ : Term σ Γ
    ρ ρ' : (Γ ─Env) Term Δ
    i : Size

-- We provide handy patterns and DISPLAY rules to hide the encoding
-- our generic-syntax library uses. Unfortunately pattern-synonyms
-- can't yet be typed in Agda.

infixl 10 _`∙_
pattern `λ' b     = (Lam _ _ , b , refl)
pattern _`∙'_ f t = (App _ _ , f , t , refl)
pattern `λ  b     = `con (`λ' b)
pattern _`∙_ f t  = `con (f `∙' t)

{-# DISPLAY `con (Lam _ _ , b , refl)     = `λ b   #-}
{-# DISPLAY `con (App _ _ , f , t , refl) = f `∙ t #-}

-- The Typed Reduction relation can be defined in the usual fashion
-- thanks to the pattern synonyms introduced above. Its reflexive
-- transitive closure is obtained by instantiating the standard
-- library's Star.

infix 3 _⊢_∋_↝_ _⊢_∋_↝⋆_
data _⊢_∋_↝_ Γ : ∀ τ → Term τ Γ → Term τ Γ → Set where
-- computational
  β    : ∀ t (u : Term σ Γ) → Γ ⊢ τ ∋ `λ t `∙ u ↝ t [ u /0]
-- structural
  [λ]  : (σ ∷ Γ) ⊢ τ ∋ t ↝ u → Γ ⊢ σ ⇒ τ ∋ `λ t ↝ `λ u
  [∙]₁ : ∀ f → Γ ⊢ σ ∋ t ↝ u → Γ ⊢ τ ∋ f `∙ t ↝ f `∙ u
  [∙]₂ : Γ ⊢ σ ⇒ τ ∋ f ↝ g → ∀ t → Γ ⊢ τ ∋ f `∙ t ↝ g `∙ t

_⊢_∋_↝⋆_ : ∀ Γ σ → Term σ Γ → Term σ Γ → Set
Γ ⊢ σ ∋ t ↝⋆ u = Star (Γ ⊢ σ ∋_↝_) t u

-- Lemma 1.2
-- Stability of Reduction under thinning and substitution
-- (Stability of Typing is a consequence of Term being a typed syntax)

th^↝ : ∀ ρ → Γ ⊢ σ ∋ t ↝ u → Δ ⊢ σ ∋ ren ρ t ↝ ren ρ u
th^↝ ρ (β t u)    = subst (_ ⊢ _ ∋ ren ρ (`λ t `∙ u) ↝_) (renβ TermD t (ε ∙ u) ρ) (β _ _)
th^↝ ρ ([λ] r)    = [λ] (th^↝ _ r)
th^↝ ρ ([∙]₁ f r) = [∙]₁ (ren ρ f) (th^↝ ρ r)
th^↝ ρ ([∙]₂ r t) = [∙]₂ (th^↝ ρ r) (ren ρ t)

-- Lemma 1.3
sub^↝ : ∀ ρ → Γ ⊢ σ ∋ t ↝ u → Δ ⊢ σ ∋ sub ρ t ↝ sub ρ u
sub^↝ ρ (β t u)    = subst (_ ⊢ _ ∋ sub ρ (`λ t `∙ u) ↝_) (subβ TermD t (ε ∙ u) ρ) (β _ _)
sub^↝ ρ ([λ] r)    = [λ] (sub^↝ _ r)
sub^↝ ρ ([∙]₁ f r) = [∙]₁ (sub ρ f) (sub^↝ ρ r)
sub^↝ ρ ([∙]₂ r t) = [∙]₂ (sub^↝ ρ r) (sub ρ t)

[/0]^↝ : (σ ∷ Γ) ⊢ τ ∋ b ↝ b′ → ∀ u → Γ ⊢ τ ∋ b [ u /0] ↝ b′ [ u /0]
[/0]^↝ r u = sub^↝ (u /0]) r

-- Lemma 1.4
↝⋆ᴿ : Rel Term Term
rel ↝⋆ᴿ σ = _ ⊢ σ ∋_↝⋆_

[v↦t↝⋆t] : {ρ : (Γ ─Env) Term Δ} → R.All ↝⋆ᴿ Γ ρ ρ
lookupᴿ [v↦t↝⋆t] k = S.ε

-- 1., 2., 3., 4.: cf. Star's gmap
-- 5.
sub^↝⋆ : (t : Term σ Γ) → R.All ↝⋆ᴿ Γ ρ ρ' → Δ ⊢ σ ∋ sub ρ t ↝⋆ sub ρ' t
sub^↝⋆ t ρᴿ = Simulation.sim sim ρᴿ t where

  sim : Simulation TermD Sub Sub ↝⋆ᴿ ↝⋆ᴿ
  Simulation.thᴿ  sim = λ ρ → S.gmap _ (th^↝ ρ)
  Simulation.varᴿ sim = id
  Simulation.algᴿ sim  {ρᴬ = ρ₁} {ρᴮ = ρ₂} = λ where
    (f `∙' t) ρᴿ (refl , fᴿ , tᴿ , _) → S.gmap _ (λ f → [∙]₂ f (sub ρ₁ t)) fᴿ
                                   S.◅◅ S.gmap _ ([∙]₁ (sub ρ₂ f)) tᴿ
    (`λ' b) ρᴿ (refl , bᴿ , _) → S.gmap `λ [λ] (bᴿ _ [v↦t↝⋆t])

[/0]^↝⋆ : ∀ t → Γ ⊢ σ ∋ u ↝ u′ → Γ ⊢ τ ∋ t [ u /0] ↝⋆ t [ u′ /0]
[/0]^↝⋆ t r = sub^↝⋆ t ([v↦t↝⋆t] ∙ᴿ S.return r)

-- Inversion lemmas for the interaction between ren, ∙, λ and ↝

th⁻¹^`∙ : ∀ (u : Term τ Γ) (ρ : Thinning Γ Δ) → f `∙ t ≡ ren ρ u →
          ∃ λ f′ → ∃ λ t′ → f′ `∙ t′ ≡ u × f ≡ ren ρ f′ × t ≡ ren ρ t′
th⁻¹^`∙ (f′ `∙ t′) ρ refl = f′ , t′ , refl , refl , refl

th⁻¹^`λ : ∀ (u : Term (σ ⇒ τ) Γ) (ρ : Thinning Γ Δ) → `λ b ≡ ren ρ u →
          ∃ λ b′ → `λ b′ ≡ u × b ≡ ren (lift vl^Var (σ ∷ []) ρ) b′
th⁻¹^`λ (`λ b′) ρ refl = b′ , refl , refl

th⁻¹^↝ : ∀ t (ρ : Thinning Γ Δ) → Δ ⊢ σ ∋ ren ρ t ↝ u′ →
         ∃ λ u → u′ ≡ ren ρ u × Γ ⊢ σ ∋ t ↝ u
th⁻¹^↝ (`λ b `∙ t) ρ (β _ _) = b [ t /0] , renβ TermD b (ε ∙ t) ρ , β b t
th⁻¹^↝ (`λ t)      ρ ([λ] r) =
  let (t′ , eq , r′) = th⁻¹^↝ t _ r in `λ t′ , cong `λ eq , [λ] r′
th⁻¹^↝ (f `∙ t) ρ ([∙]₁ ._ r) =
  let (t′ , eq , r′) = th⁻¹^↝ t ρ r in f `∙ t′ , cong (ren ρ f `∙_) eq , [∙]₁ _ r′
th⁻¹^↝ (f `∙ t) ρ ([∙]₂ r ._) =
  let (f′ , eq , r′) = th⁻¹^↝ f ρ r in f′ `∙ t , cong (_`∙ ren ρ t) eq , [∙]₂ r′ _

th⁻¹^↝⋆ : ∀ t ρ → Δ ⊢ σ ∋ ren ρ t ↝⋆ u′ →
          ∃ λ u → u′ ≡ ren ρ u × Γ ⊢ σ ∋ t ↝⋆ u
th⁻¹^↝⋆ {σ = σ} t ρ rs = go t ρ refl rs where

  go : ∀ t ρ → ∀ {t′ u′} → t′ ≡ ren ρ t → Δ ⊢ σ ∋ t′ ↝⋆ u′ →
       ∃ λ u → u′ ≡ ren ρ u × Γ ⊢ σ ∋ t ↝⋆ u
  go t ρ refl Star.ε        = t , refl , Star.ε
  go t ρ refl (r Star.◅ rs) =
    let (u , eq , r′)   = th⁻¹^↝ t ρ r in
    let (v , eq′ , rs′) = go u ρ eq rs in
    v , eq′ , r′ Star.◅ rs′

-- Section 4 Defining Strongly Normalizing Terms
-------------------------------------------------------------------

-- Section 3.1 Definition of Strong Normalization via Accessibility Relation
-- Inductive definition of Strong Normalisation as the least set of
-- terms closed under reduction

Closed : (Term σ Γ → Term σ Γ → Set) →
         (Term σ Γ → Set) → (Term σ Γ → Set)
Closed red R t = ∀ {u} → red t u → R u

-- Definition 3.1
infix 3 _⊢sn_∋_<_ _⊢sn_∋_
data _⊢sn_∋_<_ Γ σ (t : Term σ Γ) : Size → Set where
  sn : Closed (Γ ⊢ σ ∋_↝_) (Γ ⊢sn σ ∋_< i) t → Γ ⊢sn σ ∋ t < ↑ i

_⊢sn_∋_ = _⊢sn_∋_< _

Closed-sn : Γ ⊢sn σ ∋ t → Closed (Γ ⊢ σ ∋_↝_) (Γ ⊢sn σ ∋_) t
Closed-sn (sn t^SN) = t^SN

-- Lemma 4.1 Closure of sn under ↝⋆
Closed⋆-sn : Γ ⊢sn σ ∋ t → Closed (Γ ⊢ σ ∋_↝⋆_) (Γ ⊢sn σ ∋_) t
Closed⋆-sn t^SN Star.ε        = t^SN
Closed⋆-sn t^SN (r Star.◅ rs) = Closed⋆-sn (Closed-sn t^SN r) rs

-- Lemma 4.2 Weakening of strongly normalizing terms
th^sn : ∀ ρ → Γ ⊢sn σ ∋ t → Δ ⊢sn σ ∋ ren ρ t
th^sn ρ (sn t^SN) = sn $ λ r →
  let (_ , eq , r′) = th⁻¹^↝ _ ρ r
  in subst (_ ⊢sn _ ∋_) (sym eq) $ th^sn ρ (t^SN r′)

-- Lemma 4.3 Anti-renaming (Strengthening) of strongly normalizing terms
th⁻¹^sn : ∀ ρ → Δ ⊢sn σ ∋ ren ρ t → Γ ⊢sn σ ∋ t
th⁻¹^sn ρ (sn tρ^sn) = sn (λ r → th⁻¹^sn ρ (tρ^sn (th^↝ ρ r)))

-- Lemma 4.4 Properties of strongly normalizing terms

-- 1.
sub⁻¹^sn : ∀ t ρ → Δ ⊢sn σ ∋ (sub ρ t) → Γ ⊢sn σ ∋ t
sub⁻¹^sn t ρ (sn tρ^sn) = sn (λ r → sub⁻¹^sn _ ρ (tρ^sn (sub^↝ ρ r)))

[/0]⁻¹^sn : ∀ t u → Γ ⊢sn τ ∋ (t [ u /0]) → (σ ∷ Γ) ⊢sn τ ∋ t
[/0]⁻¹^sn t u t[u]^sn = sub⁻¹^sn t (u /0]) t[u]^sn

-- 2.
`λ^sn : (σ ∷ Γ) ⊢sn τ ∋ t → Γ ⊢sn σ ⇒ τ ∋ `λ t
`λ^sn (sn tᴿ) = sn λ { ([λ] r) → `λ^sn (tᴿ r) }

-- 3.
`∙t⁻¹^sn : Γ ⊢sn τ ∋ (f `∙ t) < i → Γ ⊢sn σ ⇒ τ ∋ f < i
`∙t⁻¹^sn (sn ft^sn) = sn (λ r → `∙t⁻¹^sn (ft^sn ([∙]₂ r _)))

f`∙⁻¹^sn : Γ ⊢sn τ ∋ (f `∙ t) < i → Γ ⊢sn σ ∋ t < i
f`∙⁻¹^sn (sn ft^sn) = sn (λ r → f`∙⁻¹^sn (ft^sn ([∙]₁ _ r)))

`∙⁻¹^sn : Γ ⊢sn τ ∋ (f `∙ t) < i → Γ ⊢sn σ ⇒ τ ∋ f < i × Γ ⊢sn σ ∋ t < i
`∙⁻¹^sn ft^sn = `∙t⁻¹^sn ft^sn , f`∙⁻¹^sn ft^sn

-- 4.
`λ⁻¹^sn : Γ ⊢sn σ ⇒ τ ∋ `λ t < i → (σ ∷ Γ) ⊢sn τ ∋ t < i
`λ⁻¹^sn (sn λt^sn) = sn (λ r → `λ⁻¹^sn (λt^sn ([λ] r)))

-- Evaluation contexts indexed by the Scope, the type of the hole, and the
-- type of the overall expression.

infix 3 _∣_⊢_ _∣_⊢[_]_∋_<_ _∣_⊢[_]_∋_ _∣_⊢sn_∋_
data _∣_⊢_ Γ ⊡ : Type → Set where
  <>  : Γ ∣ ⊡ ⊢ ⊡
  app : Γ ∣ ⊡ ⊢ σ ⇒ τ → Term σ Γ → Γ ∣ ⊡ ⊢ τ

data _∣_⊢[_]_∋_<_ Γ ⊡ (R : ∀ Γ σ → Term σ Γ → Size → Set) : ∀ τ (c : Γ ∣ ⊡ ⊢ τ) → Size → Set where
  <>  : Γ ∣ ⊡ ⊢[ R ] ⊡ ∋ <> < ↑ i
  app : ∀ {c} → Γ ∣ ⊡ ⊢[ R ] σ ⇒ τ ∋ c < i → R Γ σ t i → Γ ∣ ⊡ ⊢[ R ] τ ∋ app c t < ↑ i

_∣_⊢[_]_∋_ = _∣_⊢[_]_∋_< _
_∣_⊢sn_∋_ = _∣_⊢[ _⊢sn_∋_<_ ]_∋_

cut : ∀ {⊡} → Term ⊡ Γ → Γ ∣ ⊡ ⊢ σ → Term σ Γ
cut t <>        = t
cut t (app c u) = cut t c `∙ u

-- Lemma 4.5 Multi-step Reductions with Evaluation Contexts
cut^↝ : ∀ c → Γ ⊢ ⊡ ∋ t ↝ u → Γ ⊢ σ ∋ cut t c ↝ cut u c
cut^↝ <>        r = r
cut^↝ (app c t) r = [∙]₂ (cut^↝ c r) t

cut^↝⋆ : ∀ c → Γ ⊢ ⊡ ∋ t ↝⋆ u → Γ ⊢ σ ∋ cut t c ↝⋆ cut u c
cut^↝⋆ c = S.gmap (flip cut c) (cut^↝ c)

-- Lemma 4.6 Evaluation Contexts
-- Neutrality in the sense of Girard: not (value constructor)-headed
data Neutral {Γ σ} : Term σ Γ → Set where
  var : ∀ v → Neutral (`var v)
  app : ∀ {τ} f (t : Term τ Γ) → Neutral (f `∙ t)

cut⁻¹‿sn^↝ : ∀ {Γ ⊡ σ u c t} → Γ ∣ ⊡ ⊢sn σ ∋ c → Neutral t → Γ ⊢ σ ∋ cut t c ↝ u →
               (∃ λ t′ → u ≡ cut t′ c × Γ ⊢ ⊡ ∋ t ↝ t′)
             ⊎ (∃ λ c′ → u ≡ cut t c′ × Γ ∣ ⊡ ⊢sn σ ∋ c′
               × ∀ t′ → Γ ⊢ σ ∋ cut t′ c ↝ cut t′ c′)
-- reduction in the plugged subterm
cut⁻¹‿sn^↝ <> ne r = inj₁ (_ , refl , r)
-- no redexes at the interface thanks to Girard neutrality
cut⁻¹‿sn^↝ (app <> t^sn) () (β b t)
-- reduction in the context
cut⁻¹‿sn^↝ (app c^sn t^sn) ne ([∙]₁ _ r) =
  inj₂ (_ , refl , app c^sn (Closed-sn t^sn r) , λ u → [∙]₁ _ r)
-- structural cases: reduction happens deeper
cut⁻¹‿sn^↝ (app c^sn t^sn) ne ([∙]₂ r t) with cut⁻¹‿sn^↝ c^sn ne r
... | inj₁ (t′ , eq , r′)         = inj₁ (t′ , cong (_`∙ t) eq , r′)
... | inj₂ (c′ , eq , c′^sn , r′) =
  inj₂ (app c′ t , cong (_`∙ t) eq , app c′^sn t^sn , λ u → [∙]₂ (r′ u) t)

cut⁻¹^↝ : ∀ {Γ ⊡ σ u} c {v : Var ⊡ Γ} → Γ ⊢ σ ∋ cut (`var v) c ↝ u →
          ∃ λ c′ → u ≡ cut (`var v) c′
cut⁻¹^↝ (app <> t) ([∙]₁ _ r)  = app <> _ , refl
cut⁻¹^↝ (app c t)  ([∙]₁ _ r)  = app c _ , refl
cut⁻¹^↝ (app c t)  ([∙]₂ r .t) =
  let (c′ , r′) = cut⁻¹^↝ c r in app c′ _ , cong (_`∙ _) r′

cut⁻¹^sn : ∀ {Γ ⊡ σ} t c → Γ ⊢sn σ ∋ cut t c → (Γ ∣ ⊡ ⊢sn σ ∋ c) × (Γ ⊢sn ⊡ ∋ t)
cut⁻¹^sn t <>        t^sn     = <> , t^sn
cut⁻¹^sn t (app c u) c[t]u^sn =
  let (c[t]^sn , u^sn) = `∙⁻¹^sn c[t]u^sn in
  let (c^sn , t^sn) = cut⁻¹^sn t c c[t]^sn in app c^sn u^sn , t^sn

-- Lemma 4.7 Closure properties of neutral terms
-- 1.
`var^sne : ∀ {σ Γ} v → Γ ⊢sn σ ∋ `var v
`var^sne v = sn (λ ())

-- 2.
`∙^sne : ∀ {Γ ⊡ σ τ t} {v : Var ⊡ Γ} c → Γ ⊢sn σ ⇒ τ ∋ cut (`var v) c → Γ ⊢sn σ ∋ t →
         Γ ⊢sn τ ∋ cut (`var v) (app c t)
`∙^sne c f^sne t^sn = sn (go c f^sne t^sn) where

  go : ∀ {Γ ⊡ σ τ t} {v : Var ⊡ Γ} c → Γ ⊢sn σ ⇒ τ ∋ cut (`var v) c → Γ ⊢sn σ ∋ t →
       Closed (Γ ⊢ τ ∋_↝_) (Γ ⊢sn τ ∋_) (cut (`var v) (app c t))
  go <>        f^sne      t^sn      ([∙]₂ () t)
  go c         f^sne      (sn t^sn) ([∙]₁ _ r) = sn (go c f^sne (t^sn r))
  go c         (sn f^sne) t^sn      ([∙]₂ r t) =
    let (c′ , eq) = cut⁻¹^↝ c r in
    let r′ = subst (_ ⊢ _ ∋ _ ↝_) eq r in
    subst (λ g → _ ⊢sn _ ∋ g `∙ t) (sym eq) (sn (go c′ (f^sne r′) t^sn))

cut^sn : ∀ {Γ ⊡ σ} v {c} → Γ ∣ ⊡ ⊢sn σ ∋ c → Γ ⊢sn σ ∋ cut (`var v) c
cut^sn v           <>              = `var^sne v
cut^sn v {app c t} (app c^sn t^sn) = `∙^sne c (cut^sn v c^sn) t^sn


-- Lemma 4.8 Composition of evaluation contexts
_∘C_ : ∀ {Γ ⊡ β σ} → Γ ∣ β ⊢ σ → Γ ∣ ⊡ ⊢ β → Γ ∣ ⊡ ⊢ σ
<>      ∘C c′ = c′
app c t ∘C c′ = app (c ∘C c′) t

cut-∘C : ∀ {Γ ⊡ β σ} t (c : Γ ∣ β ⊢ σ) (c′ : Γ ∣ ⊡ ⊢ β) →
         cut (cut t c′) c ≡ cut t (c ∘C c′)
cut-∘C t <>        c′ = refl
cut-∘C t (app c u) c′ = cong (_`∙ u) (cut-∘C t c c′)

∘Cᴿ : ∀ {Γ ⊡ R β σ c c′} → Γ ∣ β ⊢[ R ] σ ∋ c → Γ ∣ ⊡ ⊢[ R ] β ∋ c′ → Γ ∣ ⊡ ⊢[ R ] σ ∋ c ∘C c′
∘Cᴿ <>              c′ᴿ = c′ᴿ
∘Cᴿ (app cᴿ tᴿ) c′ᴿ = app (∘Cᴿ cᴿ c′ᴿ) tᴿ

-- Lemma 4.9
β⁻¹^Closed-sn : ∀ {Γ ⊡ σ τ} c b u → (σ ∷ Γ) ⊢sn ⊡ ∋ b → Γ ⊢sn σ ∋ u →
                Γ ⊢sn τ ∋ cut (b [ u /0]) c → Γ ∣ ⊡ ⊢sn τ ∋ c →
                Closed (Γ ⊢ τ ∋_↝_) (Γ ⊢sn τ ∋_) (cut (`λ b `∙ u) c)
β⁻¹^Closed-sn c b u b^sn@(sn b^sn′) u^sn@(sn u^sn′) c[b[u]]^sn@(sn c[b[u]]^sn′) c^sn r
  with cut⁻¹‿sn^↝ c^sn (app (`λ b) u) r
... | inj₁ (._ , refl , β .b .u)          = c[b[u]]^sn
... | inj₁ (._ , refl , [∙]₁ .(`λ b) r′)  =
  let c[b[u]]^sn′ = Closed⋆-sn c[b[u]]^sn (cut^↝⋆ c ([/0]^↝⋆ b r′)) in
  sn (β⁻¹^Closed-sn c b _ b^sn (u^sn′ r′) c[b[u]]^sn′ c^sn)
... | inj₁ (._ , refl , [∙]₂ ([λ] r′) .u) =
  sn (β⁻¹^Closed-sn c _ u (b^sn′ r′) u^sn (c[b[u]]^sn′ (cut^↝ c ([/0]^↝ r′ u))) c^sn)
... | inj₂ (c′ , refl , c′^sn , r′) =
  sn (β⁻¹^Closed-sn c′ b u b^sn u^sn (c[b[u]]^sn′ (r′ (b [ u /0]))) c′^sn)

β⁻¹^sn : ∀ {Γ ⊡ σ τ b u c} → (σ ∷ Γ) ⊢sn ⊡ ∋ b → Γ ⊢sn σ ∋ u →
         Γ ⊢sn τ ∋ cut (b [ u /0]) c → Γ ∣ ⊡ ⊢sn τ ∋ c →
         Γ ⊢sn τ ∋ cut (`λ b `∙ u) c
β⁻¹^sn b^sn u^sn c[b[u]]^sn c^sn = sn (β⁻¹^Closed-sn _ _ _ b^sn u^sn c[b[u]]^sn c^sn)

-- Section 3.2 Inductive Definition of Strongly Normalizing Terms

infix 5 _⊢_∋_↝SN_<_ _⊢SN_∋_<_ _⊢SNe_∋_<_
data _⊢_∋_↝SN_<_ Γ τ : Term τ Γ → Term τ Γ → Size → Set
data _⊢SN_∋_<_ (Γ : List Type) : (σ : Type) → Term σ Γ → Size → Set
data _⊢SNe_∋_<_ (Γ : List Type) : (σ : Type) → Term σ Γ → Size → Set

data _⊢_∋_↝SN_<_ Γ τ where
-- computational
  β    : ∀ {σ i} t u → Γ ⊢SN σ ∋ u < i → Γ ⊢ τ ∋ `λ t `∙ u ↝SN t [ u /0] < ↑ i
-- structural
  [∙]₂ : ∀ {σ i f g} → Γ ⊢ σ ⇒ τ ∋ f ↝SN g < i → ∀ t → Γ ⊢ τ ∋ f `∙ t ↝SN g `∙ t < ↑ i

data _⊢SN_∋_<_ Γ where
  neu : ∀ {σ t i} → Γ ⊢SNe σ ∋ t < i → Γ ⊢SN σ ∋ t < ↑ i
  lam : ∀ {σ τ b i} → (σ ∷ Γ) ⊢SN τ ∋ b < i → Γ ⊢SN σ ⇒ τ ∋ `λ b < ↑ i
  red : ∀ {σ t t′ i} → Γ ⊢ σ ∋ t ↝SN t′ < i → Γ ⊢SN σ ∋ t′ < i → Γ ⊢SN σ ∋ t < ↑ i

data _⊢SNe_∋_<_ Γ where
  var : ∀ {σ i} v → Γ ⊢SNe σ ∋ `var v < ↑ i
  app : ∀ {σ τ f t i} → Γ ⊢SNe σ ⇒ τ ∋ f < i → Γ ⊢SN σ ∋ t < i → Γ ⊢SNe τ ∋ f `∙ t < ↑ i

infix 5 _⊢_∋_↝SN_ _⊢SN_∋_ _⊢SNe_∋_
_⊢_∋_↝SN_ = _⊢_∋_↝SN_< _
_⊢SN_∋_ = _⊢SN_∋_< _
_⊢SNe_∋_ = _⊢SNe_∋_< _

SN∋ : Pred Term
pred SN∋ = _ ⊢SN_∋_

SNe : Pred Term
pred SNe = _ ⊢SNe_∋_

[v↦v]^SNe : ∀ {Γ} → P.All SNe _ (base vl^Tm {Γ})
lookupᴾ [v↦v]^SNe v rewrite lookup-base^Tm {d = TermD} v = var v

infix 4 _∣_⊢SN_∋_<_ _∣_⊢SN_∋_
_∣_⊢SN_∋_<_ = _∣_⊢[ _⊢SN_∋_<_ ]_∋_<_
_∣_⊢SN_∋_ = _∣_⊢SN_∋_< _

cut⁻¹^SNe : ∀ {Γ τ t i} → Γ ⊢SNe τ ∋ t < i →
  Σ[ ctx ∈ (∃ λ σ → Γ ∣ σ ⊢ τ) ] let (σ , c) = ctx in
            ∃ λ v → t ≡ cut (`var v) c × Γ ∣ σ ⊢SN τ ∋ c < i
cut⁻¹^SNe (var v)          = _ , v , refl , <>
cut⁻¹^SNe (app f^SNe t^SN) =
  let (_ , v , eq , c^SN) = cut⁻¹^SNe f^SNe
  in _ , v , cong (_`∙ _) eq , app c^SN t^SN

-- Lemma 4.11 Thinning
mutual

 -- 1.
 th^SN : ∀ {σ Γ Δ t} ρ → Γ ⊢SN σ ∋ t → Δ ⊢SN σ ∋ ren ρ t
 th^SN ρ (neu n)   = neu (th^SNe ρ n)
 th^SN ρ (lam t)   = lam (th^SN _ t)
 th^SN ρ (red r t) = red (th^↝SN ρ r) (th^SN ρ t)

 -- 2.
 th^SNe : ∀ {σ Γ Δ t} ρ → Γ ⊢SNe σ ∋ t → Δ ⊢SNe σ ∋ ren ρ t
 th^SNe ρ (var v)   = var (lookup ρ v)
 th^SNe ρ (app n t) = app (th^SNe ρ n) (th^SN ρ t)

 -- 3.
 th^↝SN : ∀ {σ Γ Δ t u} ρ → Γ ⊢ σ ∋ t ↝SN u → Δ ⊢ σ ∋ ren ρ t ↝SN ren ρ u
 th^↝SN ρ (β t u u^SN) = subst (_ ⊢ _ ∋ ren ρ (`λ t `∙ u) ↝SN_< _) (renβ TermD t (ε ∙ u) ρ)
                       $ β _ (ren ρ u) (th^SN ρ u^SN)
 th^↝SN ρ ([∙]₂ r t)   = [∙]₂ (th^↝SN ρ r) (ren ρ t)

-- Lemma 4.12 Anti-Thinning

mutual

 -- 1.
 th⁻¹^SN : ∀ {σ Γ Δ t′} t ρ → t′ ≡ ren ρ t → Δ ⊢SN σ ∋ t′ → Γ ⊢SN σ ∋ t
 th⁻¹^SN t        ρ eq    (neu pr)    = neu (th⁻¹^SNe t ρ eq pr)
 th⁻¹^SN (`λ t)   ρ refl  (lam pr)    = lam (th⁻¹^SN t _ refl pr)
 th⁻¹^SN t        ρ refl  (red r pr)  =
   let (t′ , eq , r′) = th⁻¹^↝SN t ρ r in red r′ (th⁻¹^SN t′ ρ eq pr)

 -- 2.
 th⁻¹^SNe : ∀ {σ Γ Δ t′} t ρ → t′ ≡ ren ρ t → Δ ⊢SNe σ ∋ t′ → Γ ⊢SNe σ ∋ t
 th⁻¹^SNe (`var v) ρ refl (var _)     = var v
 th⁻¹^SNe (f `∙ t) ρ refl (app rf rt) =
  app (th⁻¹^SNe f ρ refl rf) (th⁻¹^SN t ρ refl rt)

 -- 3.
 th⁻¹^↝SN : ∀ {σ Γ Δ u} t ρ → Δ ⊢ σ ∋ ren ρ t ↝SN u → ∃ λ u′ → u ≡ ren ρ u′ × Γ ⊢ σ ∋ t ↝SN u′
 th⁻¹^↝SN (`λ b `∙ t) ρ (β ._ ._ t^SN) = b [ t /0] , renβ TermD b (ε ∙ t) ρ , β b t (th⁻¹^SN t ρ refl t^SN)
 th⁻¹^↝SN (f `∙ t)    ρ ([∙]₂ r ._)    =
   let (g , eq , r′) = th⁻¹^↝SN f ρ r in g `∙ t , cong (_`∙ ren ρ t) eq , [∙]₂ r′ t

-- Lemma 4.13 SNe is closed under application
_SNe∙_ : ∀ {Γ σ τ f t} → Γ ⊢SNe σ ⇒ τ ∋ f → Γ ⊢SN σ ∋ t → Γ ⊢SN τ ∋ f `∙ t
f^SNe SNe∙ t^SN = neu (app f^SNe t^SN)

-- Lemma 4.14: Extensionality of SN
SNe-ext : ∀ {Γ σ τ f} v → Γ ⊢SNe τ ∋ f `∙ `var v → Γ ⊢SNe σ ⇒ τ ∋ f
SNe-ext v (app f^SNe v^SN) = f^SNe

SN-ext : ∀ {Γ σ τ f} v → Γ ⊢SN τ ∋ f `∙ `var v → Γ ⊢SN σ ⇒ τ ∋ f
SN-ext v (neu fv^SNe)   = neu (SNe-ext v fv^SNe)
SN-ext v (red ([∙]₂ r .(`var v))   fv^SN) = red r (SN-ext v fv^SN)
SN-ext v (red (β t .(`var v) v^SN) fv^SN) = lam (th⁻¹^SN t (base vl^Var ∙ v) eq fv^SN) where
  eq = sym $ Simulation.sim Sim.RenSub (base^VarTmᴿ ∙ᴿ refl) t

-- Section 4.3 Soundness (Short alternative proof)
infix 4 _⊢_∋_↝sn_<_ _⊢_∋_↝sn_
data _⊢_∋_↝sn_<_ Γ τ : (t u : Term τ Γ) → Size → Set where
  β    : ∀ {σ i} b u → Γ ⊢sn σ ∋ u → Γ ⊢ τ ∋ `λ b `∙ u ↝sn b [ u /0] < ↑ i
  [∙]₂ : ∀ {σ f g i} → Γ ⊢ σ ⇒ τ ∋ f ↝sn g < i → ∀ t → Γ ⊢ τ ∋ f `∙ t ↝sn g `∙ t < ↑ i

_⊢_∋_↝sn_ = _⊢_∋_↝sn_< _

-- Lemma 4.17 Backwards closure of sn
↝sn⁻¹^sn : ∀ {Γ σ τ t′ t i} c → Γ ⊢ σ ∋ t′ ↝sn t < i →
           Γ ⊢sn τ ∋ cut t c → Γ ⊢sn τ ∋ cut t′ c
↝sn⁻¹^sn c (β b u u^sn)  c[b[u]]^sn =
  let (c^sn , b[u]^sn) = cut⁻¹^sn (b [ u /0]) c c[b[u]]^sn in
  let b^sn = [/0]⁻¹^sn b u b[u]^sn in
  β⁻¹^sn b^sn u^sn c[b[u]]^sn c^sn
↝sn⁻¹^sn c ([∙]₂ r^sn u) c[ft]^sn   =
  let eq t   = cut-∘C t c (app <> u) in
  let ft^sn′ = subst (_ ⊢sn _ ∋_) (eq _) c[ft]^sn in
  let ih     = ↝sn⁻¹^sn (c ∘C app <> u) r^sn ft^sn′ in
  subst (_ ⊢sn _ ∋_) (sym (eq _)) ih

 -- Theorem 4.18 Soundness of SN
mutual
  -- 1.
  sound^SN : ∀ {Γ σ t i} → Γ ⊢SN σ ∋ t < i → Γ ⊢sn σ ∋ t
  sound^SN (neu t^SNe)  = let (_ , v , eq , c^SN) = cut⁻¹^SNe t^SNe in
                          subst (_ ⊢sn _ ∋_) (sym eq) (cut^sn _ (sound^∣SN c^SN))
  sound^SN (lam b^SN)   = `λ^sn (sound^SN b^SN)
  sound^SN (red r t^SN) = ↝sn⁻¹^sn <> (sound^↝SN r) (sound^SN t^SN)

  -- 2.
  sound^∣SN : ∀ {Γ ⊡ σ c i} → Γ ∣ ⊡ ⊢SN σ ∋ c < i → Γ ∣ ⊡ ⊢sn σ ∋ c
  sound^∣SN <>              = <>
  sound^∣SN (app c^SN t^SN) = app (sound^∣SN c^SN) (sound^SN t^SN)

  -- 3.
  sound^↝SN : ∀ {Γ σ t u i} → Γ ⊢ σ ∋ t ↝SN u < i → Γ ⊢ σ ∋ t ↝sn u
  sound^↝SN (β t u u^SN) = β t u (sound^SN u^SN)
  sound^↝SN ([∙]₂ r t)   = [∙]₂ (sound^↝SN r) t

-- Section 4.4 Soundness and Completeness

-- Theorem 4.16 Completeness of SN

mutual
  -- 1.
  complete^SNe : ∀ {c} v → Γ ∣ ⊡ ⊢SN σ ∋ c →
                 let t = cut (`var v) c in
                 ∀ {t′} → t′ ≡ t → Γ ⊢sn σ ∋ t′ < i → Γ ⊢SNe σ ∋ t′
  complete^SNe v <>           refl c[v]^sn   = var v
  complete^SNe v (app c t^SN) refl c[v]∙t^sn =
    let (c[v]^sn , t^sn) = `∙⁻¹^sn c[v]∙t^sn in
    app (complete^SNe v c refl c[v]^sn) t^SN

  -- 2.
  complete^SN-β : ∀ (b : Term ⊡ (σ ∷ Γ)) u (c : Γ ∣ ⊡ ⊢ τ) →
                  let t = cut (`λ b `∙ u) c in Γ ⊢ τ ∋ t ↝SN cut (b [ u /0]) c →
                  ∀ {t′} → t′ ≡ t → Γ ⊢sn τ ∋ t′ < i → Γ ⊢SN τ ∋ t′
  complete^SN-β b u c r refl (sn c[λb∙u]^sn) = red r (complete^SN _ (c[λb∙u]^sn (cut^↝ c (β b u))))

  -- 3.
  complete^SN : ∀ t → Γ ⊢sn σ ∋ t < i → Γ ⊢SN σ ∋ t
  complete^SN (`var v) v^sn  = neu (var v)
  complete^SN (`λ b)   λb^sn = lam (complete^SN b (`λ⁻¹^sn λb^sn))
  complete^SN (f `∙ t) ft^sn =
    let (f^sn , t^sn) = `∙⁻¹^sn ft^sn in
    let t^SN = complete^SN t t^sn in
    case unzip f t f^sn t^SN of λ where
       (_ , c , inj₁ (v , eq , sp))        → neu (complete^SNe v sp eq ft^sn)
       (_ , c , inj₂ (_ , b , u , eq , r)) → complete^SN-β b u c r eq ft^sn

  -- ugly but it works
  unzip : ∀ f t → Γ ⊢sn σ ⇒ τ ∋ f < i → Γ ⊢SN σ ∋ t →
          ∃ λ ⊡ → ∃ λ (c : Γ ∣ ⊡ ⊢ τ) →
          (∃ λ v → f `∙ t ≡ cut (`var v) c × Γ ∣ ⊡ ⊢SN τ ∋ c)
        ⊎ (∃ λ β → ∃ λ (b : Term ⊡ (β ∷ Γ)) → ∃ λ u →
             f `∙ t ≡ cut (`λ b `∙ u) c
             × Γ ⊢ τ ∋ cut (`λ b `∙ u) c ↝SN cut (b [ u /0]) c)
  unzip (`var v) t v^sn  t^SN = _ , app <> t , inj₁ (v , refl , app <> t^SN)
  unzip (`λ b)   t λb^sn t^SN = _ , <> , inj₂ (_ , b , t , refl , β b t t^SN)
  unzip (f `∙ u) t fu^sn t^SN =
    let (f^sn , u^sn) = `∙⁻¹^sn fu^sn in
    let u^SN = complete^SN u u^sn in
    case unzip f u f^sn u^SN of λ where
      (_ , c , inj₁ (v , eq , sp)) →
        _ , app c t , inj₁ (v , cong (_`∙ t) eq , app sp t^SN)
      (_ , c , inj₂ (_ , b , a , eq , r)) →
        _ , app c t , inj₂ (_ , b , a , cong (_`∙ t) eq , [∙]₂ r t)

-- Section 5 Reducibility Candidates
-------------------------------------------------------------------

infix 3 _⊢𝓡_∋_
_⊢𝓡_∋_ : ∀ Γ σ → Term σ Γ → Set
Γ ⊢𝓡 α      ∋ t = Γ ⊢SN α ∋ t
Γ ⊢𝓡 σ ⇒ τ ∋ t = ∀ {Δ} ρ {u} → Δ ⊢𝓡 σ ∋ u → Δ ⊢𝓡 τ ∋ ren ρ t `∙ u

𝓡ᴾ : Pred Term
pred 𝓡ᴾ = _ ⊢𝓡_∋_

-- Theorem 5.1
mutual
  -- 1.
  quote^𝓡 : ∀ σ {t} → Γ ⊢𝓡 σ ∋ t → Γ ⊢SN σ ∋ t
  quote^𝓡 α        t^𝓡 = t^𝓡
  quote^𝓡 (σ ⇒ τ) t^𝓡 = th⁻¹^SN _ embed refl (SN-ext z tz^SN)
    where z^𝓡  = unquote^𝓡 σ (var z)
          embed = pack s
          tz^SN = quote^𝓡 τ (t^𝓡 embed z^𝓡)

  -- 2.
  unquote^𝓡 : ∀ σ {t} → Γ ⊢SNe σ ∋ t → Γ ⊢𝓡 σ ∋ t
  unquote^𝓡 α       t^SNe        = neu t^SNe
  unquote^𝓡 (σ ⇒ τ) t^SNe ρ u^𝓡 = unquote^𝓡 τ (app (th^SNe ρ t^SNe) u^SN)
    where u^SN = quote^𝓡 σ u^𝓡

-- 3.
↝SN⁻¹^𝓡 : ∀ σ {t′ t} → Γ ⊢ σ ∋ t′ ↝SN t → Γ ⊢𝓡 σ ∋ t → Γ ⊢𝓡 σ ∋ t′
↝SN⁻¹^𝓡 α       r t^𝓡 = red r t^𝓡
↝SN⁻¹^𝓡 (σ ⇒ τ) r t^𝓡 = λ ρ u^𝓡 → ↝SN⁻¹^𝓡 τ ([∙]₂ (th^↝SN ρ r) _) (t^𝓡 ρ u^𝓡)


th^𝓡 : ∀ σ ρ t → Γ ⊢𝓡 σ ∋ t → Δ ⊢𝓡 σ ∋ ren ρ t
th^𝓡 α       ρ t t^𝓡         = th^SN ρ t^𝓡
th^𝓡 (σ ⇒ τ) ρ t t^𝓡 ρ′ u^𝓡 = cast (t^𝓡 (select ρ ρ′) u^𝓡)
  where cast = subst (λ t → _ ⊢𝓡 _ ∋ t `∙ _) (sym $ ren² TermD t ρ ρ′)

_∙^𝓡_ : Γ ⊢𝓡 σ ⇒ τ ∋ f → Γ ⊢𝓡 σ ∋ t → Γ ⊢𝓡 τ ∋ f `∙ t
f^𝓡 ∙^𝓡 t^𝓡 = cast (f^𝓡 (base vl^Var) t^𝓡)
  where cast = subst (λ t → _ ⊢𝓡 _ ∋ t `∙ _) (ren-id _)


-- Section 6 Proving strong normalization
-------------------------------------------------------------------

-- Lemma 6.1 Fundamental lemma
fundamental : Fundamental TermD Sub 𝓡ᴾ 𝓡ᴾ
Fundamental.thᴾ  fundamental = λ ρ v^𝓡 → th^𝓡 _ ρ _ v^𝓡
Fundamental.varᴾ fundamental = λ x → x
Fundamental.algᴾ fundamental = algᴾ where

  algᴾ :  (b : ⟦ TermD ⟧ (Scope (Tm TermD i)) σ Γ) →
          let v = fmap TermD (Semantics.body Sub ρ) b in
          P.All 𝓡ᴾ _ ρ → Fdm.All TermD (Kripkeᴾ 𝓡ᴾ 𝓡ᴾ) v → Δ ⊢𝓡 σ ∋ Semantics.alg Sub v
  algᴾ (f `∙' t) ρᴾ (fᴾ , tᴾ , _)  = fᴾ ∙^𝓡 tᴾ
  algᴾ {ρ = ρ₁} (`λ' b) ρᴾ (bᴾ , _) ρ {u} u^𝓡 = ↝SN⁻¹^𝓡 _ β-step $ cast (bᴾ ρ (εᴾ ∙ᴾ u^𝓡))
  -- at this point the substitution looks HORRIBLE
    where
      β-step = β (ren _ (sub _ b)) _ (quote^𝓡 _ u^𝓡)
      ρ′  = lift vl^Var (_ ∷ []) ρ
      ρ₁′ = lift vl^Tm (_ ∷ []) ρ₁

      ρᴿ : R.All VarTmᴿ _ ρ (select (freshʳ vl^Var (_ ∷ [])) (select ρ′ (u /0])))
      lookupᴿ ρᴿ k = sym $ begin
        lookup (base vl^Tm) (lookup (base vl^Var) (lookup ρ (lookup (base vl^Var) k)))
          ≡⟨ lookup-base^Tm _ ⟩
        `var (lookup (base vl^Var) (lookup ρ (lookup (base vl^Var) k)))
          ≡⟨ cong `var (lookup-base^Var _) ⟩
        `var (lookup ρ (lookup (base vl^Var) k))
          ≡⟨ cong (`var ∘ lookup ρ) (lookup-base^Var k) ⟩
        `var (lookup ρ k) ∎

      ρᴿ′ : R.All Eqᴿ _ (sub (select ρ′ (u /0])) <$> ρ₁′) ((ε ∙ u) >> th^Env th^Tm ρ₁ ρ)
      lookupᴿ ρᴿ′ z     = refl
      lookupᴿ ρᴿ′ (s k) = begin
        sub (select ρ′ (u /0])) (ren _ (lookup ρ₁ k)) ≡⟨ rensub TermD (lookup ρ₁ k) _ _ ⟩
        sub _ (lookup ρ₁ k)                           ≡⟨ sym $ Simulation.sim Sim.RenSub ρᴿ (lookup ρ₁ k) ⟩
        ren ρ (lookup ρ₁ k) ∎

      eq : sub ((ε ∙ u) >> th^Env th^Tm ρ₁ ρ) b ≡ ren ρ′ (sub ρ₁′ b) [ u /0]
      eq = sym $ begin
        ren ρ′ (sub ρ₁′ b) [ u /0]           ≡⟨ rensub TermD (sub ρ₁′ b) ρ′ (u /0]) ⟩
        sub (select ρ′ (u /0])) (sub ρ₁′ b)  ≡⟨ Fusion.fusion (Sub² TermD) ρᴿ′ b ⟩
        sub ((ε ∙ u) >> th^Env th^Tm ρ₁ ρ) b ∎

      cast = subst (_ ⊢𝓡 _ ∋_) eq

eval : P.All 𝓡ᴾ _ ρ → (t : Term σ Γ) → Δ ⊢𝓡 σ ∋ sub ρ t
eval = Fundamental.fundamental fundamental

-- Corollary 6.2
dummy : P.All 𝓡ᴾ Γ (base vl^Tm)
lookupᴾ dummy v rewrite lookup-base^Tm {d = TermD} v = unquote^𝓡 _ (var v)

_^SN : ∀ t → Γ ⊢SN σ ∋ t
t ^SN = cast (quote^𝓡 _ (eval dummy t))
  where cast  = subst (_ ⊢SN _ ∋_) (sub-id t)

_^sn : ∀ t → Γ ⊢sn σ ∋ t
t ^sn = sound^SN (t ^SN)
\end{code}

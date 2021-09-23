\begin{code}
{-# OPTIONS --safe --sized-types #-}
module Motivation.POPLMark2.STLC where

open import Data.Var using (Var; _─Scoped; injectˡ; injectʳ)
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
open import Data.List.Base hiding ([_] ; lookup)
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

private
  variable
    σ τ : Type
    ⊡ ⊡₁ ⊡₂ : Type
    Γ Δ : List Type
    t t′ u u′ f g b b′ : Term σ Γ
    ρ ρ′ : (Γ ─Env) Term Δ
    i : Size

-- We provide handy patterns and DISPLAY rules to hide the encoding
-- our generic-syntax library uses. Unfortunately pattern-synonyms
-- can't yet be typed in Agda.

infixl 10 _`∙_
pattern `λ' b     = (Lam _ _ , b , refl)
pattern _`∙'_ f t = (App _ _ , f , t , refl)

pattern `λ  b    = `con (`λ' b)
pattern _`∙_ f t = `con (f `∙' t)

{-# DISPLAY `con (Lam _ _ , b , refl)     = `λ b        #-}
{-# DISPLAY `con (App _ _ , f , t , refl) = f `∙ t      #-}

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
th^↝ ρ (β t u)      = subst (_ ⊢ _ ∋ ren ρ (`λ t `∙ u) ↝_) (renβ TermD t (ε ∙ u) ρ) (β _ _)
th^↝ ρ ([λ] r)      = [λ] (th^↝ _ r)
th^↝ ρ ([∙]₁ f r)   = [∙]₁ (ren ρ f) (th^↝ ρ r)
th^↝ ρ ([∙]₂ r t)   = [∙]₂ (th^↝ ρ r) (ren ρ t)

-- Lemma 1.3
sub^↝ : ∀ ρ → Γ ⊢ σ ∋ t ↝ u → Δ ⊢ σ ∋ sub ρ t ↝ sub ρ u
sub^↝ ρ (β t u)      = subst (_ ⊢ _ ∋ sub ρ (`λ t `∙ u) ↝_) (subβ TermD t (ε ∙ u) ρ) (β _ _)
sub^↝ ρ ([λ] r)      = [λ] (sub^↝ _ r)
sub^↝ ρ ([∙]₁ f r)   = [∙]₁ (sub ρ f) (sub^↝ ρ r)
sub^↝ ρ ([∙]₂ r t)   = [∙]₂ (sub^↝ ρ r) (sub ρ t)

[/0]^↝ : ∀ {σ τ Γ b b′} → (σ ∷ Γ) ⊢ τ ∋ b ↝ b′ → ∀ u → Γ ⊢ τ ∋ b [ u /0] ↝ b′ [ u /0]
[/0]^↝ r u = sub^↝ (u /0]) r

-- Lemma 1.4
↝⋆ᴿ : Rel Term Term
rel ↝⋆ᴿ = _ ⊢_∋_↝⋆_

[v↦t↝⋆t] : {ρ : (Γ ─Env) Term Δ} → R.All ↝⋆ᴿ Γ ρ ρ
lookupᴿ [v↦t↝⋆t] k = S.ε

-- 1., 2., 3., 4.: cf. Star's gmap
-- 5.
sub^↝⋆ : ∀ t → R.All ↝⋆ᴿ Γ ρ ρ′ → Δ ⊢ σ ∋ sub ρ t ↝⋆ sub ρ′ t
sub^↝⋆ t ρᴿ = Simulation.sim sim ρᴿ t where

  sim : Simulation TermD Sub Sub ↝⋆ᴿ ↝⋆ᴿ
  Simulation.thᴿ  sim = λ ρ → S.gmap _ (th^↝ ρ)
  Simulation.varᴿ sim = id
  Simulation.algᴿ sim {ρᴬ = ρ₁} {ρᴮ = ρ₂} = λ where
    (f `∙' t) ρᴿ (refl , fᴿ , tᴿ , _) → S.gmap _ (λ f → [∙]₂ f (sub ρ₁ t)) fᴿ
                                                S.◅◅ S.gmap _ ([∙]₁ (sub ρ₂ f)) tᴿ
    (`λ' b) ρᴿ (refl , bᴿ , _) → S.gmap `λ [λ] (bᴿ _ [v↦t↝⋆t])

[/0]^↝⋆ : ∀ {σ τ Γ} t {u u′} → Γ ⊢ σ ∋ u ↝ u′ → Γ ⊢ τ ∋ t [ u /0] ↝⋆ t [ u′ /0]
[/0]^↝⋆ t r = sub^↝⋆ t ([v↦t↝⋆t] ∙ᴿ S.return r)

-- Inversion lemmas for the interaction between ren, ∙, λ and ↝

th⁻¹^`∙ : ∀ (u : Term τ Γ) {f : Term (σ ⇒ τ) Δ} {t} ρ → f `∙ t ≡ ren ρ u →
          ∃ λ f′ → ∃ λ t′ → f′ `∙ t′ ≡ u × f ≡ ren ρ f′ × t ≡ ren ρ t′
th⁻¹^`∙ (f′ `∙ t′)     ρ refl = f′ , t′ , refl , refl , refl

th⁻¹^`λ : ∀ (u : Term (σ ⇒ τ) Γ) {b : Term τ (σ ∷ Δ)} ρ → `λ b ≡ ren ρ u →
          ∃ λ b′ → `λ b′ ≡ u × b ≡ ren (lift vl^Var (σ ∷ []) ρ) b′
th⁻¹^`λ (`λ b′)        ρ refl = b′ , refl , refl

th⁻¹^↝ : ∀ t ρ → Δ ⊢ σ ∋ ren ρ t ↝ u′ →
         ∃ λ u → u′ ≡ ren ρ u × Γ ⊢ σ ∋ t ↝ u
-- redex
th⁻¹^↝ (`λ b `∙ t)           ρ (β _ _)    = b [ t /0] , renβ TermD b (ε ∙ t) ρ , β b t
-- structural
th⁻¹^↝ (`λ t)      ρ ([λ] r) =
  let (t′ , eq , r′) = th⁻¹^↝ t _ r in `λ t′ , cong `λ eq , [λ] r′
th⁻¹^↝ (f `∙ t) ρ ([∙]₁ ._ r) =
  let (t′ , eq , r′) = th⁻¹^↝ t ρ r in f `∙ t′ , cong (ren ρ f `∙_) eq , [∙]₁ _ r′
th⁻¹^↝ (f `∙ t) ρ ([∙]₂ r ._) =
  let (f′ , eq , r′) = th⁻¹^↝ f ρ r in f′ `∙ t , cong (_`∙ ren ρ t) eq , [∙]₂ r′ _

th⁻¹^↝⋆ : ∀ t ρ → Δ ⊢ σ ∋ ren ρ t ↝⋆ u′ →
          ∃ λ u → u′ ≡ ren ρ u × Γ ⊢ σ ∋ t ↝⋆ u
th⁻¹^↝⋆ t ρ rs = go t ρ refl rs where

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
         (Term σ Γ → Set) → Term σ Γ → Set
Closed red R t = ∀ {u} → red t u → R u

Closed⇒Closed⋆ : ∀ {red R} → (∀ {t : Term σ Γ} → R t → Closed red R t) →
                 ∀ {t} → R t → Closed (Star red) R t
Closed⇒Closed⋆ cl tᴿ Star.ε        = tᴿ
Closed⇒Closed⋆ cl tᴿ (r Star.◅ rs) = Closed⇒Closed⋆ cl (cl tᴿ r) rs

-- Definition 3.1
infix 3 _⊢sn_∋_<_ _⊢sn_∋_
data _⊢sn_∋_<_ Γ σ (t : Term σ Γ) : Size → Set where
  sn : Closed (Γ ⊢ σ ∋_↝_) (Γ ⊢sn σ ∋_< i) t → Γ ⊢sn σ ∋ t < ↑ i

_⊢sn_∋_ = _⊢sn_∋_< _

Closed-sn : Γ ⊢sn σ ∋ t → Closed (Γ ⊢ σ ∋_↝_) (Γ ⊢sn σ ∋_) t
Closed-sn (sn t^SN) = t^SN

-- Lemma 4.1 Closure of sn under ↝⋆
Closed⋆-sn : Γ ⊢sn σ ∋ t → Closed (Γ ⊢ σ ∋_↝⋆_) (Γ ⊢sn σ ∋_) t
Closed⋆-sn = Closed⇒Closed⋆ Closed-sn

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

data _∣_⊢[_]_∋_<_ Γ ⊡ (R : ∀ Γ σ → Term σ Γ → Size → Set) : ∀ σ → Γ ∣ ⊡ ⊢ σ → Size → Set where
  <>  : Γ ∣ ⊡ ⊢[ R ] ⊡ ∋ <> < ↑ i
  app : ∀ {c} → Γ ∣ ⊡ ⊢[ R ] σ ⇒ τ ∋ c < i → R Γ σ t i → Γ ∣ ⊡ ⊢[ R ] τ ∋ app c t < ↑ i

_∣_⊢[_]_∋_ = _∣_⊢[_]_∋_< _
_∣_⊢sn_∋_ = _∣_⊢[ _⊢sn_∋_<_ ]_∋_

cut : Term ⊡ Γ → Γ ∣ ⊡ ⊢ σ → Term σ Γ
cut t <>        = t
cut t (app c u) = cut t c `∙ u

-- Lemma 4.5 Multi-step Reductions with Evaluation Contexts
cut^↝ : ∀ c → Γ ⊢ ⊡ ∋ t ↝ u → Γ ⊢ σ ∋ cut t c ↝ cut u c
cut^↝ <>        red = red
cut^↝ (app c t) red = [∙]₂ (cut^↝ c red) t

cut^↝⋆ : ∀ c → Γ ⊢ ⊡ ∋ t ↝⋆ u → Γ ⊢ σ ∋ cut t c ↝⋆ cut u c
cut^↝⋆ c = S.gmap (flip cut c) (cut^↝ c)

-- Lemma 4.6 Evaluation Contexts
-- Neutrality in the sense of Girard: not (value constructor)-headed
data Neutral {Γ ν} : Term ν Γ → Set where
  var : ∀ v → Neutral (`var v)
  app : ∀ f (t : Term τ Γ) → Neutral (f `∙ t)

cut⁻¹‿sn^↝ : ∀ {c} → Γ ∣ ⊡ ⊢sn σ ∋ c → Neutral t → Γ ⊢ σ ∋ cut t c ↝ u →
               (∃ λ t′ → u ≡ cut t′ c × Γ ⊢ ⊡ ∋ t ↝ t′)
             ⊎ (∃ λ c′ → u ≡ cut t c′ × Γ ∣ ⊡ ⊢sn σ ∋ c′
               × ∀ t′ → Γ ⊢ σ ∋ cut t′ c ↝ cut t′ c′)
-- reduction in the plugged subterm
cut⁻¹‿sn^↝ <> ne r = inj₁ (_ , refl , r)
-- no redexes at the interface thanks to Girard neutrality
cut⁻¹‿sn^↝ (app <> t^sn)      () (β b t)
-- reduction in the context
cut⁻¹‿sn^↝ (app c^sn t^sn) ne ([∙]₁ _ r) =
  inj₂ (_ , refl , app c^sn (Closed-sn t^sn r) , λ u → [∙]₁ _ r)
cut⁻¹‿sn^↝ (app c^sn t^sn) ne ([∙]₂ r t) with cut⁻¹‿sn^↝ c^sn ne r
... | inj₁ (t′ , eq , r′)         = inj₁ (t′ , cong (_`∙ t) eq , r′)
... | inj₂ (c′ , eq , c′^sn , r′) =
  inj₂ (app c′ t , cong (_`∙ t) eq , app c′^sn t^sn , λ u → [∙]₂ (r′ u) t)

cut⁻¹^↝ : ∀ c {v : Var ⊡ Γ} → Γ ⊢ σ ∋ cut (`var v) c ↝ u →
          ∃ λ c′ → u ≡ cut (`var v) c′
cut⁻¹^↝ (app <> t) ([∙]₁ _ r)   = app <> _ , refl
cut⁻¹^↝ (app c t)  ([∙]₁ _ r)   = app c _ , refl
cut⁻¹^↝ (app c t)  ([∙]₂ r _)   =
  let (c′ , eq) = cut⁻¹^↝ c r in app c′ _ , cong (_`∙ _) eq

cut⁻¹^sn : ∀ t c → Γ ⊢sn σ ∋ cut t c → (Γ ∣ ⊡ ⊢sn σ ∋ c) × (Γ ⊢sn ⊡ ∋ t)
cut⁻¹^sn t <>        t^sn     = <> , t^sn
cut⁻¹^sn t (app c u) c[t]u^sn =
  let (c[t]^sn , u^sn) = `∙⁻¹^sn c[t]u^sn in
  let (c^sn , t^sn) = cut⁻¹^sn t c c[t]^sn in app c^sn u^sn , t^sn

-- Lemma 4.7 Closure properties of neutral terms
-- 1.
`var^sne : ∀ v → Γ ⊢sn σ ∋ `var v
`var^sne v = sn (λ ())

-- 2.
`∙^sne : ∀ {v : Var ⊡ Γ} c → Γ ⊢sn σ ⇒ τ ∋ cut (`var v) c → Γ ⊢sn σ ∋ t →
         Γ ⊢sn τ ∋ cut (`var v) (app c t)
`∙^sne c f^sne t^sn = sn (go c f^sne t^sn) where

  go : ∀ {v : Var ⊡ Γ} c → Γ ⊢sn σ ⇒ τ ∋ cut (`var v) c → Γ ⊢sn σ ∋ t →
       Closed (Γ ⊢ τ ∋_↝_) (Γ ⊢sn τ ∋_) (cut (`var v) (app c t))
  go <>        f^sne      t^sn      ([∙]₂ () t)
  go c         f^sne      (sn t^sn) ([∙]₁ _ r) = sn (go c f^sne (t^sn r))
  go c         (sn f^sne) t^sn      ([∙]₂ r t) =
    let (c′ , eq) = cut⁻¹^↝ c r in let r′ = subst (_ ⊢ _ ∋ _ ↝_) eq r in
    subst (λ g → _ ⊢sn _ ∋ g `∙ t) (sym eq) (sn (go c′ (f^sne r′) t^sn))


cut^sn : ∀ v {c} → Γ ∣ ⊡ ⊢sn σ ∋ c → Γ ⊢sn σ ∋ cut (`var v) c
cut^sn v           <>              = `var^sne v
cut^sn v {app c t} (app c^sn t^sn) = `∙^sne c (cut^sn v c^sn) t^sn

-- Lemma 4.8 Composition of evaluation contexts
_∘C_ : Γ ∣ ⊡₂ ⊢ σ → Γ ∣ ⊡₁ ⊢ ⊡₂ → Γ ∣ ⊡₁ ⊢ σ
<>      ∘C c′ = c′
app c t ∘C c′ = app (c ∘C c′) t

cut-∘C : ∀ t (c : Γ ∣ ⊡₂ ⊢ σ) (c′ : Γ ∣ ⊡₁ ⊢ ⊡₂) →
         cut (cut t c′) c ≡ cut t (c ∘C c′)
cut-∘C t <>        c′ = refl
cut-∘C t (app c u) c′ = cong (_`∙ u) (cut-∘C t c c′)

∘Cᴿ : ∀ {R c c′} → Γ ∣ ⊡₂ ⊢[ R ] σ ∋ c → Γ ∣ ⊡₁ ⊢[ R ] ⊡₂ ∋ c′ → Γ ∣ ⊡₁ ⊢[ R ] σ ∋ c ∘C c′
∘Cᴿ <>          c′ᴿ = c′ᴿ
∘Cᴿ (app cᴿ tᴿ) c′ᴿ = app (∘Cᴿ cᴿ c′ᴿ) tᴿ

-- β or ι redexes
infix 3 _⊢↯_ _⊢↯sn_∋_
data _⊢↯_ (Γ : List Type) (τ : Type) : Set where
  β  : Term τ (σ ∷ Γ) → Term σ Γ → Γ ⊢↯ τ

-- Notion of sn for redexes: all the redex's components are sn
-- We defined this one by case analysis on Γ ⊢↯ τ because that seems to be easier
-- on the termination checker.
_⊢↯sn_∋_ : ∀ Γ τ → Γ ⊢↯ τ → Set
Γ ⊢↯sn τ ∋ β b u    = (_ ∷ Γ) ⊢sn τ ∋ b × Γ ⊢sn _ ∋ u

-- Pre and Post firing of the redex.
-- * Pre-firing we have a Girard-neutral.
-- * Pre and Post are naturally linked via Typed Reduction as fire demonstrates
unRed : Γ ⊢↯ τ → Term τ Γ
unRed (β b u)    = `λ b `∙ u

unRed^Neutral : (r : Γ ⊢↯ τ) → Neutral (unRed r)
unRed^Neutral (β b u)    = app (`λ b) u

βιRed : Γ ⊢↯ τ → Term τ Γ
βιRed (β b u)    = b [ u /0]

fire : ∀ r → Γ ⊢ τ ∋ unRed r ↝ βιRed r
fire (β b u)    = β b u

-- Closure under fire-expansion
c[fire]⁻¹^Closed-sn : ∀ {c} r → Γ ⊢↯sn ⊡ ∋ r → Γ ∣ ⊡ ⊢sn σ ∋ c →
  Γ ⊢sn σ ∋ cut (βιRed r) c → Closed (Γ ⊢ σ ∋_↝_) (Γ ⊢sn σ ∋_) (cut (unRed r) c)
c[fire⁻¹]^Closed-sn : ∀ c r → Γ ⊢↯sn ⊡ ∋ r → Γ ∣ ⊡ ⊢sn σ ∋ c →
  Γ ⊢sn σ ∋ cut (βιRed r) c → ∀ {t} → Γ ⊢ ⊡ ∋ unRed r ↝ t → Γ ⊢sn σ ∋ cut t c

c[fire]⁻¹^Closed-sn r r^sn c^sn c[r]^sn@(sn c[r]^sn′) red
  with cut⁻¹‿sn^↝ c^sn (unRed^Neutral r) red
... | inj₁ (_ , refl , r′) = c[fire⁻¹]^Closed-sn _ r r^sn c^sn c[r]^sn r′
... | inj₂ (c′ , refl , c′^sn , red′) =
  sn (c[fire]⁻¹^Closed-sn r r^sn c′^sn (c[r]^sn′ (red′ (βιRed r))))

-- Either the redex does fire
c[fire⁻¹]^Closed-sn c (β _ _)    _ c^sn c[r]^sn (β _ _)    = c[r]^sn

-- Or we are in a structural case
-- β redex
c[fire⁻¹]^Closed-sn c (β b u) (b^sn , sn u^sn) c^sn c[r]^sn ([∙]₁ _ red) =
  let c[r′]^sn = Closed⋆-sn c[r]^sn (cut^↝⋆ c ([/0]^↝⋆ b red)) in
  sn (c[fire]⁻¹^Closed-sn (β b _) (b^sn , u^sn red) c^sn c[r′]^sn)
c[fire⁻¹]^Closed-sn c (β b u) (sn b^sn , u^sn) c^sn c[r]^sn ([∙]₂ ([λ] red) t) =
  let c[r′]^sn = Closed-sn c[r]^sn (cut^↝ c ([/0]^↝ red u)) in
  sn (c[fire]⁻¹^Closed-sn (β _ u) (b^sn red , u^sn) c^sn c[r′]^sn)

c[fire⁻¹]^sn : ∀ {c} r → Γ ⊢↯sn ⊡ ∋ r → Γ ∣ ⊡ ⊢sn σ ∋ c →
               Γ ⊢sn σ ∋ cut (βιRed r) c → Γ ⊢sn σ ∋ cut (unRed r) c
c[fire⁻¹]^sn r r^sn c^sn c[r]^sn = sn (c[fire]⁻¹^Closed-sn r r^sn c^sn c[r]^sn)

-- Section 3.2 Inductive Definition of Strongly Normalizing Terms
-- TODO: refactor computational part as: Γ ⊢↯ τ + R-constraints?
infix 4 _⊢[_]_∋_↝_<_
data _⊢[_]_∋_↝_<_ Γ (R : ∀ Γ σ → Term σ Γ → Size → Set) τ : (t u : Term τ Γ) → Size → Set where
-- computational
  β    : ∀ t u → R Γ σ u i → Γ ⊢[ R ] τ ∋ `λ t `∙ u ↝ t [ u /0] < ↑ i
-- structural
  [∙]₂ : Γ ⊢[ R ] σ ⇒ τ ∋ f ↝ g < i → ∀ t → Γ ⊢[ R ] τ ∋ f `∙ t ↝ g `∙ t < ↑ i

infix 4 _⊢_∋_↝SN_<_ _⊢SN_∋_<_ _⊢SNe_∋_<_ _⊢_∋_↝SN_ _⊢SN_∋_ _⊢SNe_∋_
_⊢_∋_↝SN_<_ : ∀ Γ τ (t u : Term τ Γ) → Size → Set
data _⊢SN_∋_<_ (Γ : List Type) : (σ : Type) → Term σ Γ → Size → Set
data _⊢SNe_∋_<_ (Γ : List Type) : (σ : Type) → Term σ Γ → Size → Set

_⊢_∋_↝SN_<_ = _⊢[ _⊢SN_∋_<_ ]_∋_↝_<_

data _⊢SN_∋_<_ Γ where
  neu : Γ ⊢SNe σ ∋ t < i → Γ ⊢SN σ ∋ t < ↑ i
  lam : (σ ∷ Γ) ⊢SN τ ∋ b < i → Γ ⊢SN σ ⇒ τ ∋ `λ b < ↑ i
  red : Γ ⊢ σ ∋ t ↝SN t′ < i → Γ ⊢SN σ ∋ t′ < i → Γ ⊢SN σ ∋ t < ↑ i

data _⊢SNe_∋_<_ Γ where
  var : ∀ v → Γ ⊢SNe σ ∋ `var v < ↑ i
  app : Γ ⊢SNe σ ⇒ τ ∋ f < i → Γ ⊢SN σ ∋ t < i → Γ ⊢SNe τ ∋ f `∙ t < ↑ i

_⊢_∋_↝SN_ = _⊢_∋_↝SN_< _
_⊢SN_∋_ = _⊢SN_∋_< _
_⊢SNe_∋_ = _⊢SNe_∋_< _

SN∋ : Pred Term
pred SN∋ = _ ⊢SN_∋_

SNe : Pred Term
pred SNe = _ ⊢SNe_∋_

[v↦v]^SNe : P.All SNe Γ (base vl^Tm)
lookupᴾ [v↦v]^SNe v rewrite lookup-base^Tm {d = TermD} v = var v

infix 4 _∣_⊢SN_∋_<_ _∣_⊢SN_∋_
_∣_⊢SN_∋_<_ = _∣_⊢[ _⊢SN_∋_<_ ]_∋_<_
_∣_⊢SN_∋_ = _∣_⊢SN_∋_< _

cut⁻¹^SNe : Γ ⊢SNe τ ∋ t < i →
  Σ[ ctx ∈ (∃ λ σ → Γ ∣ σ ⊢ τ) ] let (σ , c) = ctx in
            ∃ λ v → t ≡ cut (`var v) c × Γ ∣ σ ⊢SN τ ∋ c < i
cut⁻¹^SNe (var v)          = _ , v , refl , <>
cut⁻¹^SNe (app f^SNe t^SN) =
  let (_ , v , eq , c^SN) = cut⁻¹^SNe f^SNe
  in _ , v , cong (_`∙ _) eq , app c^SN t^SN

-- Lemma 4.11 Thinning
mutual

 -- 1.
 th^SN : ∀ ρ → Γ ⊢SN σ ∋ t → Δ ⊢SN σ ∋ ren ρ t
 th^SN ρ (neu n)   = neu (th^SNe ρ n)
 th^SN ρ (lam t)   = lam (th^SN _ t)
 th^SN ρ (red r t) = red (th^↝SN ρ r) (th^SN ρ t)

 -- 2.
 th^SNe : ∀ ρ → Γ ⊢SNe σ ∋ t → Δ ⊢SNe σ ∋ ren ρ t
 th^SNe ρ (var v)       = var (lookup ρ v)
 th^SNe ρ (app n t)     = app (th^SNe ρ n) (th^SN ρ t)

 -- 3.
 th^↝SN : ∀ ρ → Γ ⊢ σ ∋ t ↝SN u → Δ ⊢ σ ∋ ren ρ t ↝SN ren ρ u
 -- computational
 th^↝SN ρ (β t u u^SN)            =
   subst (_ ⊢ _ ∋ ren ρ (`λ t `∙ u) ↝SN_< _) (renβ TermD t (ε ∙ u) ρ) (β _ (ren ρ u) (th^SN ρ u^SN))
 -- structural
 th^↝SN ρ ([∙]₂ r t)     = [∙]₂ (th^↝SN ρ r) (ren ρ t)

freshˡ^SNe : P.All SNe Γ (freshˡ vl^Tm Δ)
lookupᴾ freshˡ^SNe k = th^SNe (pack (injectˡ _)) (cast (var k))
  where cast = subst (_ ⊢SNe _ ∋_) (sym (lookup-base^Tm k))

-- Lemma 4.12 Anti-Thinning
mutual

 -- 1.
 th⁻¹^SN : ∀ t ρ → t′ ≡ ren ρ t → Δ ⊢SN σ ∋ t′ → Γ ⊢SN σ ∋ t
 th⁻¹^SN t      ρ eq    (neu pr) = neu (th⁻¹^SNe t ρ eq pr)
 th⁻¹^SN (`λ t) ρ refl  (lam pr) = lam (th⁻¹^SN t _ refl pr)
 th⁻¹^SN t      ρ refl  (red r pr)  =
   let (t′ , eq , r′) = th⁻¹^↝SN t ρ r in red r′ (th⁻¹^SN t′ ρ eq pr)

 -- 2.
 th⁻¹^SNe : ∀ t ρ → t′ ≡ ren ρ t → Δ ⊢SNe σ ∋ t′ → Γ ⊢SNe σ ∋ t
 th⁻¹^SNe (`var v) ρ refl (var _)     = var v
 th⁻¹^SNe (f `∙ t) ρ refl (app rf rt) =
   app (th⁻¹^SNe f ρ refl rf) (th⁻¹^SN t ρ refl rt)

 -- 3.
 th⁻¹^↝SN : ∀ t ρ → Δ ⊢ σ ∋ ren ρ t ↝SN u → ∃ λ u′ → u ≡ ren ρ u′ × Γ ⊢ σ ∋ t ↝SN u′
 -- reductions
 th⁻¹^↝SN (`λ b `∙ t) ρ (β ._ ._ t^SN) =
   b [ t /0] , renβ TermD b (ε ∙ t) ρ , β b t (th⁻¹^SN t ρ refl t^SN)
-- structural
 th⁻¹^↝SN (f `∙ t)        ρ ([∙]₂ r ._)    =
   let (g , eq , r′) = th⁻¹^↝SN f ρ r in g `∙ t , cong (_`∙ ren ρ t) eq , [∙]₂ r′ t

-- Lemma 4.13 SNe is closed under application
_SNe∙_ : Γ ⊢SNe σ ⇒ τ ∋ f → Γ ⊢SN σ ∋ t → Γ ⊢SN τ ∋ f `∙ t
f^SNe SNe∙ t^SN = neu (app f^SNe t^SN)

-- Lemma 4.14: Extensionality of SN
SNe-ext : ∀ v → Γ ⊢SNe τ ∋ f `∙ `var v → Γ ⊢SNe σ ⇒ τ ∋ f
SNe-ext v (app f^SNe v^SN) = f^SNe

SN-ext : ∀ v → Γ ⊢SN τ ∋ f `∙ `var v → Γ ⊢SN σ ⇒ τ ∋ f
SN-ext v (neu fv^SNe)             = neu (SNe-ext v fv^SNe)
SN-ext v (red ([∙]₂ r _)   fv^SN) = red r (SN-ext v fv^SN)
SN-ext v (red (β t _ v^SN) fv^SN) = lam (th⁻¹^SN t (base vl^Var ∙ v) eq fv^SN) where
  eq = sym $ Simulation.sim Sim.RenSub (base^VarTmᴿ ∙ᴿ refl) t

-- Section 4.3 Soundness (Short alternative proof)
infix 4 _⊢_∋_↝sn_<_ _⊢_∋_↝sn_
_⊢_∋_↝sn_<_ = _⊢[ _⊢sn_∋_<_ ]_∋_↝_<_
_⊢_∋_↝sn_ = _⊢_∋_↝sn_< _

-- Lemma 4.17 Backwards closure of sn
↝sn⁻¹^sn : ∀ c → Γ ⊢ σ ∋ t′ ↝sn t < i →
           Γ ⊢sn τ ∋ cut t c → Γ ⊢sn τ ∋ cut t′ c
-- computational
↝sn⁻¹^sn c (β b u u^sn) c[b[u]]^sn =
  let (c^sn , b[u]^sn) = cut⁻¹^sn (b [ u /0]) c c[b[u]]^sn in
  let b^sn = [/0]⁻¹^sn b u b[u]^sn in
  c[fire⁻¹]^sn (β b u) (b^sn , u^sn) c^sn c[b[u]]^sn
-- structural
↝sn⁻¹^sn c ([∙]₂ r^sn u) c[ft]^sn =
  let eq t   = cut-∘C t c (app <> u) in
  let ft^sn′ = subst (_ ⊢sn _ ∋_) (eq _) c[ft]^sn in
  let ih     = ↝sn⁻¹^sn (c ∘C app <> u) r^sn ft^sn′ in
  subst (_ ⊢sn _ ∋_) (sym (eq _)) ih

 -- Theorem 4.18 Soundness of SN
mutual
 -- 1.
 sound^SN : Γ ⊢SN σ ∋ t < i → Γ ⊢sn σ ∋ t
 sound^SN (neu t^SNe)  = let (_ , v , eq , c^SN) = cut⁻¹^SNe t^SNe in
                         subst (_ ⊢sn _ ∋_) (sym eq) (cut^sn _ (sound^∣SN c^SN))
 sound^SN (lam b^SN)   = `λ^sn (sound^SN b^SN)
 sound^SN (red r t^SN) = ↝sn⁻¹^sn <> (sound^↝SN r) (sound^SN t^SN)

 -- 2.
 sound^∣SN : ∀ {c} → Γ ∣ ⊡ ⊢SN σ ∋ c < i → Γ ∣ ⊡ ⊢sn σ ∋ c
 sound^∣SN <>              = <>
 sound^∣SN (app c^SN t^SN) = app (sound^∣SN c^SN) (sound^SN t^SN)

 -- 3.
 sound^↝SN : Γ ⊢ σ ∋ t ↝SN u < i → Γ ⊢ σ ∋ t ↝sn u
 sound^↝SN (β t u u^SN) = β t u (sound^SN u^SN)
 sound^↝SN ([∙]₂ r t)   = [∙]₂ (sound^↝SN r) t

-- Section 4.4 Soundness and Completeness

-- Theorem 4.16 Completeness of SN
-- We start with a definition of deeply nested β-redexes

data Elim (Γ : List Type) (τ : Type) : Type → Set where
  app : Term σ Γ → Elim Γ τ (σ ⇒ τ)

elim : Elim Γ τ σ → Γ ∣ σ ⊢ τ
elim (app t)     = app <> t

mutual
  -- 1.
  complete^SNe : ∀ {c} v → Γ ∣ ⊡ ⊢SN σ ∋ c →
    let t = cut (`var v) c in ∀ {t′} → t′ ≡ t → Γ ⊢sn σ ∋ t′ < i → Γ ⊢SNe σ ∋ t′
  complete^SNe v <>           refl c[v]^sn   = var v
  complete^SNe v (app c t^SN) refl c[v]∙t^sn =
    app (complete^SNe v c refl (`∙t⁻¹^sn c[v]∙t^sn)) t^SN

  -- 2.
  complete^SN-βι : ∀ (r : Γ ⊢↯ ⊡) c →
    let t = cut (unRed r) c in Γ ⊢ σ ∋ t ↝SN cut (βιRed r) c →
    ∀ {t′} → t′ ≡ t → Γ ⊢sn σ ∋ t′ < i → Γ ⊢SN σ ∋ t′
  complete^SN-βι t c r refl (sn p) = red r (complete^SN _ (p (cut^↝ c (fire t))))

  -- 3.
  complete^SN : ∀ t → Γ ⊢sn σ ∋ t < i → Γ ⊢SN σ ∋ t
  complete^SN (`var v) v^sn  = neu (var v)
  complete^SN (`λ b)   λb^sn = lam (complete^SN b (`λ⁻¹^sn λb^sn))
  complete^SN (f `∙ t) ft^sn =
    let (f^sn , t^sn) = `∙⁻¹^sn ft^sn in
    let t^SN = complete^SN t t^sn in
    elim^SN f (app t) f^sn (app <> t^SN) ft^sn

  elim^SN : ∀ t e → Γ ⊢sn σ ∋ t < i → Γ ∣ σ ⊢SN τ ∋ elim e →
            Γ ⊢sn τ ∋ cut t (elim e) < i → Γ ⊢SN τ ∋ cut t (elim e)
  elim^SN t e t^sn e^SN e[t]^sn =
    case spine^SN t e t^sn e^SN of λ where
      (_ , c , inj₁ (v , eq , c^SN)) → neu (complete^SNe v c^SN eq e[t]^sn)
      (_ , c , inj₂ (r , eq , r^SN)) → complete^SN-βι r c r^SN eq e[t]^sn

  spine^SN : ∀ t e → Γ ⊢sn σ ∋ t < i → Γ ∣ σ ⊢SN τ ∋ elim e →
             ∃ λ ⊡ → ∃ λ (c : Γ ∣ ⊡ ⊢ τ) →
      (∃ λ v → cut t (elim e) ≡ cut (`var v) c × Γ ∣ ⊡ ⊢SN τ ∋ c)
    ⊎ (∃ λ r → cut t (elim e) ≡ cut (unRed r) c
             × Γ ⊢ τ ∋ cut (unRed r) c ↝SN cut (βιRed r) c)
  -- redex
  spine^SN (`var v) e tm^sn e^SN = _ , elim e , inj₁ (v , refl , e^SN)
  spine^SN (`λ b) (app t) tm^sn (app <> t^SN) = _ , <> , inj₂ (β b t , refl , β b t t^SN)
  -- structural (TODO: refactor?)
  spine^SN (f `∙ t) e tm^sn e^SN =
    let (f^sn , t^sn) = `∙⁻¹^sn tm^sn in
    let t^SN = complete^SN t t^sn in
    case spine^SN f (app t) f^sn (app <> t^SN) of λ where
      (_ , c , inj₁ (v , eq , c^SN)) →
        _ , (elim e ∘C c) , inj₁ (v , spine-eq e c eq , ∘Cᴿ e^SN c^SN)
      (_ , c , inj₂ (r , eq , r^SN)) →
        _ , (elim e ∘C c) , inj₂ (r , spine-eq e c eq , spine-red e c r r^SN)

  spine-eq : ∀ {t tc} (e : Elim Γ σ ⊡₂) (c : Γ ∣ ⊡₁ ⊢ ⊡₂) →
             tc ≡ cut t c → cut tc (elim e) ≡ cut t (elim e ∘C c)
  spine-eq e c refl = cut-∘C _ (elim e) c

  spine-red : ∀ e c → (r : Γ ⊢↯ ⊡₁) →
              Γ ⊢ ⊡₂ ∋ cut (unRed r) c ↝SN cut (βιRed r) c →
              Γ ⊢ σ ∋ cut (unRed r) (elim e ∘C c) ↝SN cut (βιRed r) (elim e ∘C c)
  spine-red (app t) c r r^SN = [∙]₂ r^SN t

-- Section 5 Reducibility Candidates
-------------------------------------------------------------------

infix 2 <_>
data <_> (𝓢 : Term σ Γ → Set) (t : Term σ Γ) : Set where
  cnd : 𝓢 t → < 𝓢 > t
  neu : Γ ⊢SNe σ ∋ t → < 𝓢 > t
  red : Γ ⊢ σ ∋ t ↝SN t′ → < 𝓢 > t′ → < 𝓢 > t

infix 3 _⊢𝓡_∋_
_⊢𝓡_∋_     : ∀ Γ σ → Term σ Γ → Set
Γ ⊢𝓡 α     ∋ t = Γ ⊢SN α ∋ t
Γ ⊢𝓡 σ ⇒ τ ∋ t = ∀ {Δ} ρ {u} → Δ ⊢𝓡 σ ∋ u → Δ ⊢𝓡 τ ∋ ren ρ t `∙ u

𝓡ᴾ : Pred Term
pred 𝓡ᴾ = _ ⊢𝓡_∋_

Quote : List Type → Type → Set
Quote Γ σ = ∀ {t} → Γ ⊢𝓡 σ ∋ t → Γ ⊢SN σ ∋ t

-- Theorem 5.1
quote^<>  : ∀ {𝓢} → (∀ {t} → 𝓢 t → Γ ⊢SN σ ∋ t) →
            ∀ {t} → < 𝓢 > t → Γ ⊢SN σ ∋ t
quote^<> σ^𝓡 (cnd t^𝓡)   = σ^𝓡 t^𝓡
quote^<> σ^𝓡 (neu t^SNe)  = neu t^SNe
quote^<> σ^𝓡 (red r t^𝓡) = red r (quote^<> σ^𝓡 t^𝓡)

mutual

 -- 1.
 quote^𝓡 : ∀ σ → Quote Γ σ
 quote^𝓡 α       t^𝓡         = t^𝓡
 quote^𝓡 (σ ⇒ τ) t^𝓡         = th⁻¹^SN _ embed refl (SN-ext Var.z tz^SN)
   where z^𝓡  = unquote^𝓡 σ (var Var.z)
         embed = pack Var.s
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

th^<> : {𝓢 : ∀ {Γ} → Term σ Γ → Set}
        (th^𝓢 : ∀ {Γ Δ t} (ρ : Thinning Γ Δ) → 𝓢 t → 𝓢 (ren ρ t)) →
        ∀ {Γ Δ t} (ρ : Thinning Γ Δ) → < 𝓢 > t → < 𝓢 > (ren ρ t)
th^<> th^𝓢 ρ (cnd t^𝓢)   = cnd (th^𝓢 ρ t^𝓢)
th^<> th^𝓢 ρ (neu t^SNe)  = neu (th^SNe ρ t^SNe)
th^<> th^𝓢 ρ (red r t^𝓢) = red (th^↝SN ρ r) (th^<> th^𝓢 ρ t^𝓢)

th^𝓡 : (σ : Type) → ∀ {Γ Δ} ρ t → Γ ⊢𝓡 σ ∋ t → Δ ⊢𝓡 σ ∋ ren ρ t
th^𝓡 α       ρ t t^𝓡         = th^SN ρ t^𝓡
th^𝓡 (σ ⇒ τ) ρ t t^𝓡 ρ′ u^𝓡 = cast (t^𝓡 (select ρ ρ′) u^𝓡)
  where cast = subst (λ t → _ ⊢𝓡 _ ∋ t `∙ _) (sym $ ren² TermD t ρ ρ′)

app^𝓡 : ∀ f t → Γ ⊢𝓡 σ ⇒ τ ∋ f → Γ ⊢𝓡 σ ∋ t → Γ ⊢𝓡 τ ∋ f `∙ t
app^𝓡 f t f^𝓡 t^𝓡 = cast (f^𝓡 (base vl^Var) t^𝓡)
  where cast = subst (λ f → _ ⊢𝓡 _ ∋ f `∙ t) (ren-id f)

reify^𝓡 : ∀ Θ τ {Γ Δ i} (sc : Scope (Tm TermD i) Θ τ Γ) (ρ : (Γ ─Env) Term Δ) →
  Kripkeᴾ 𝓡ᴾ 𝓡ᴾ Θ τ (Semantics.body Sub ρ Θ τ sc) →
  (Θ ++ Δ) ⊢SN τ ∋ sub (lift vl^Tm Θ ρ) sc
reify^𝓡 []        τ sc ρ scᴾ = cast (quote^𝓡 _ scᴾ) where

  cast = subst (_ ⊢SN _ ∋_) (Simulation.sim Sim.SubExt (lift[]^Tm ρ) sc)
reify^𝓡 Θ@(_ ∷ _) τ sc ρ scᴾ = quote^𝓡 τ (scᴾ nms (nmsᴿ)) where

  nms = freshʳ vl^Var Θ

  nmsᴿ : P.All 𝓡ᴾ _ (freshˡ vl^Tm _)
  lookupᴾ nmsᴿ k = unquote^𝓡 _ (lookupᴾ freshˡ^SNe k)


sub^𝓡 : ∀ Θ τ {i Γ Δ} (sc : Scope (Tm TermD i) Θ τ Γ) (vs : (Θ ─Env) Term Δ) (ρ : (Γ ─Env) Term Δ) →
         Kripkeᴾ 𝓡ᴾ 𝓡ᴾ Θ τ (Semantics.body Sub ρ Θ τ sc) →
         P.All 𝓡ᴾ _ vs →
         Δ ⊢𝓡 τ ∋ sub (vs >> base vl^Tm) (sub (lift vl^Tm Θ ρ) sc)
sub^𝓡 [] τ sc vs ρ scᴿ vsᴿ = cast scᴿ where

  subᴿ : R.All Eqᴿ _ (sub (vs >> base vl^Tm) <$> lift vl^Tm [] ρ) ρ
  lookupᴿ subᴿ k = begin
    sub (vs >> base vl^Tm) (ren (th^Env th^Var (base vl^Var) (pack id)) (lookup ρ k))
      ≡⟨ rensub TermD (lookup ρ k) (th^Env th^Var (base vl^Var) (pack id)) (vs >> base vl^Tm) ⟩
    sub (select (th^Env th^Var (base vl^Var) (pack id)) (base vl^Tm)) (lookup ρ k)
      ≡⟨ Simulation.sim Sim.SubExt (packᴿ (λ v → cong (lookup (base vl^Tm)) (lookup-base^Var v))) (lookup ρ k) ⟩
    sub (base vl^Tm) (lookup ρ k)
      ≡⟨ sub-id (lookup ρ k) ⟩
    lookup ρ k
      ∎

  cast = subst (_ ⊢𝓡 τ ∋_) (sym (Fusion.fusion (Sub² TermD) subᴿ sc))
sub^𝓡 Θ@(_ ∷ _) τ sc vs ρ scᴿ vsᴿ = cast (scᴿ (base vl^Var) vsᴿ) where

  subᴿ : R.All Eqᴿ _ (sub (vs >> base vl^Tm) <$> lift vl^Tm Θ ρ)
                        (vs >> th^Env th^Tm ρ (base vl^Var))
  lookupᴿ subᴿ k with split Θ k
  ... | inj₁ k₁ = begin
    sub (vs >> base vl^Tm) (ren (pack (injectˡ _)) (lookup ((th^Env th^Tm (base vl^Tm) (pack Var.s)) ∙ `var Var.z) k₁))
      ≡⟨ cong (λ v → sub (vs >> base vl^Tm) (ren (pack (injectˡ _)) v)) (lookupᴿ th^base^s∙z k₁) ⟩
     sub (vs >> base vl^Tm) (ren (pack (injectˡ _)) (`var k₁))
       ≡⟨ injectˡ->> vs (base vl^Tm) k₁ ⟩
    lookup vs k₁
      ∎
  ... | inj₂ k₂ = begin
    sub (vs >> base vl^Tm) (ren (th^Env th^Var (base vl^Var) (pack (injectʳ Θ))) (lookup ρ k₂))
      ≡⟨ rensub TermD (lookup ρ k₂) (th^Env th^Var (base vl^Var) (pack (injectʳ Θ))) (vs >> base vl^Tm) ⟩
    sub (select (th^Env th^Var (base vl^Var) (pack (injectʳ Θ))) (vs >> base vl^Tm)) (lookup ρ k₂)
      ≡⟨ Simulation.sim Sim.SubExt sub'ᴿ (lookup ρ k₂) ⟩
    sub (`var <$> base vl^Var) (lookup ρ k₂)
      ≡⟨ sym (Sim.rensub (base vl^Var) (lookup ρ k₂)) ⟩
    ren (base vl^Var) (lookup ρ k₂)
      ∎ where

     sub'ᴿ : R.All Eqᴿ _ (select (th^Env th^Var (base vl^Var) (pack (injectʳ Θ))) (vs >> base vl^Tm))
                            (`var <$> base vl^Var)
     lookupᴿ sub'ᴿ k = begin
       lookup (vs >> base vl^Tm) (lookup {𝓥 = Var} (pack (injectʳ Θ)) (lookup (base vl^Var) k))
         ≡⟨ cong (λ v → lookup (vs >> base vl^Tm) (lookup {𝓥 = Var} (pack (injectʳ Θ)) v)) (lookup-base^Var k) ⟩
       lookup (vs >> base vl^Tm) (injectʳ Θ k)
         ≡⟨ injectʳ->> vs (base vl^Tm) k ⟩
       lookup (base vl^Tm) k
         ≡⟨ sym (lookupᴿ base^VarTmᴿ k) ⟩
       lookup {𝓥 = Term} (`var <$> base vl^Var) k
         ∎

  cast = subst (_ ⊢𝓡 τ ∋_) (sym (Fusion.fusion (Sub² TermD) subᴿ sc))

[/0]^𝓡 :
  ∀ σ τ {Γ Δ i} t (l : Tm TermD i τ (σ ∷ Γ)) (ρ : (Γ ─Env) Term Δ) →
  Δ ⊢𝓡 σ ∋ t →
  Kripkeᴾ 𝓡ᴾ 𝓡ᴾ (σ ∷ []) τ (Semantics.body Sub ρ (σ ∷ []) τ l) →
  Δ ⊢𝓡 τ ∋ sub (lift vl^Tm (σ ∷ []) ρ) l [ t /0]
[/0]^𝓡 σ τ t l ρ tᴾ lᴾ = cast (sub^𝓡 (σ ∷ []) τ l (ε ∙ t) ρ lᴾ (εᴾ ∙ᴾ tᴾ)) where

  subᴿ : R.All Eqᴿ _ ((ε ∙ t) >> base vl^Tm) (t /0])
  lookupᴿ subᴿ Var.z     = refl
  lookupᴿ subᴿ (Var.s v) = refl

  cast = subst (_ ⊢𝓡 τ ∋_) (Simulation.sim Sim.SubExt subᴿ (sub _ l))

-- Section 6 Proving strong normalization
-------------------------------------------------------------------

-- Lemma 6.1 Fundamental lemma
fundamental : Fundamental TermD Sub 𝓡ᴾ 𝓡ᴾ
Fundamental.thᴾ  fundamental {i = σ} {v = v} = λ ρ v^𝓡 → th^𝓡 σ ρ v v^𝓡
Fundamental.varᴾ fundamental = λ x → x
Fundamental.algᴾ fundamental = algᴾ where

  algᴾ : ∀ {ρ} (b : ⟦ TermD ⟧ (Scope (Tm TermD i)) σ Γ) →
          let v = fmap TermD (Semantics.body Sub ρ) b in
          P.All 𝓡ᴾ _ ρ → Fdm.All TermD (Kripkeᴾ 𝓡ᴾ 𝓡ᴾ) v → Δ ⊢𝓡 σ ∋ Semantics.alg Sub v
  -- eliminators
  algᴾ (f `∙' t)          ρᴾ (fᴾ , tᴾ , _)       = app^𝓡 (sub _ f) (sub _ t) fᴾ tᴾ
  -- lambda abstraction
  algᴾ {ρ = ρ₁} (`λ' b)   ρᴾ (bᴾ , _) ρ {u} u^𝓡 =
    ↝SN⁻¹^𝓡 _ β-step $ cast (bᴾ ρ (εᴾ ∙ᴾ u^𝓡))
  -- at this point the substitution looks HORRIBLE
    where
      β-step = β (ren _ (sub _ b)) _ (quote^𝓡 _ u^𝓡)
      ρ'  = lift vl^Var (_ ∷ []) ρ
      ρ₁' = lift vl^Tm (_ ∷ []) ρ₁

      ρᴿ : R.All VarTmᴿ _ ρ (select (freshʳ vl^Var (_ ∷ [])) (select ρ' (u /0])))
      lookupᴿ ρᴿ k = sym $ begin
        lookup (base vl^Tm) (lookup (base vl^Var) (lookup ρ (lookup (base vl^Var) k)))
          ≡⟨ lookup-base^Tm _ ⟩
        `var (lookup (base vl^Var) (lookup ρ (lookup (base vl^Var) k)))
          ≡⟨ cong `var (lookup-base^Var _) ⟩
        `var (lookup ρ (lookup (base vl^Var) k))
          ≡⟨ cong (`var ∘ lookup ρ) (lookup-base^Var k) ⟩
        `var (lookup ρ k) ∎

      ρᴿ' : R.All Eqᴿ _ (sub (select ρ' (u /0])) <$> ρ₁') ((ε ∙ u) >> th^Env th^Tm ρ₁ ρ)
      lookupᴿ ρᴿ' Var.z     = refl
      lookupᴿ ρᴿ' (Var.s k) = begin
        sub (select ρ' (u /0])) (ren _ (lookup ρ₁ k)) ≡⟨ rensub TermD (lookup ρ₁ k) _ _ ⟩
        sub _ (lookup ρ₁ k)                           ≡⟨ sym $ Simulation.sim Sim.RenSub ρᴿ (lookup ρ₁ k) ⟩
        ren ρ (lookup ρ₁ k) ∎

      eq : sub ((ε ∙ u) >> th^Env th^Tm ρ₁ ρ) b ≡ ren ρ' (sub ρ₁' b) [ u /0]
      eq = sym $ begin
        ren ρ' (sub ρ₁' b) [ u /0]           ≡⟨ rensub TermD (sub ρ₁' b) ρ' (u /0]) ⟩
        sub (select ρ' (u /0])) (sub ρ₁' b)  ≡⟨ Fusion.fusion (Sub² TermD) ρᴿ' b ⟩
        sub ((ε ∙ u) >> th^Env th^Tm ρ₁ ρ) b ∎

      cast = subst (_ ⊢𝓡 _ ∋_) eq

eval : ∀ {Γ Δ σ ρ} → P.All 𝓡ᴾ _ ρ → (t : Term σ Γ) → Δ ⊢𝓡 σ ∋ sub ρ t
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

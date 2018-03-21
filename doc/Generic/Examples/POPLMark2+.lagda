\begin{code}
module Generic.Examples.POPLMark2+ where

open import Generic

open import Size
open import Data.Sum as Sum
open import Data.Product as Prod
open import Agda.Builtin.List
open import Data.Product hiding (,_)
open import Data.Star as S using (Star)
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
  _+_ : Type → Type → Type
  _⇒_ : Type → Type → Type

data TermC : Set where
  Lam App  : Type → Type → TermC
  InL InR  : Type → Type → TermC
  Cas      : Type → Type → Type → TermC

TermD : Desc Type
TermD =  `σ TermC λ where
  (Lam σ τ)    → `X (σ ∷ []) τ (`∎ (σ ⇒ τ))
  (App σ τ)    → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ))
  (InL σ τ)    → `X [] σ (`∎ (σ + τ))
  (InR σ τ)    → `X [] τ (`∎ (σ + τ))
  (Cas σ τ ν)  → `X [] (σ + τ) (`X (σ ∷ []) ν (`X (τ ∷ []) ν (`∎ ν)))

Term : Type ─Scoped
Term = Tm TermD _

-- We provide handy patterns and DISPLAY rules to hide the encoding
-- our generic-syntax library uses. Unfortunately pattern-synonyms
-- can't yet be typed in Agda.

infixl 10 _`∙_
pattern `λ' b         = (Lam _ _ , b , refl)
pattern _`∙'_ f t     = (App _ _ , f , t , refl)
pattern `i₁' t        = (InL _ _ , t , refl)
pattern `i₂' t        = (InR _ _ , t , refl)
pattern `case' t l r  = (Cas _ _ _ , t , l , r , refl)
pattern `λ  b         = `con (`λ' b)
pattern _`∙_ f t      = `con (f `∙' t)
pattern `i₁ t         = `con (`i₁' t)
pattern `i₂ t         = `con (`i₂' t)
pattern `case t l r   = `con (`case' t l r)

{-# DISPLAY syn.`con (Lam _ _ , b , refl)           = `λ b        #-}
{-# DISPLAY syn.`con (App _ _ , f , t , refl)       = f `∙ t      #-}
{-# DISPLAY syn.`con (InL _ _ , t , refl)           = `i₁ t       #-}
{-# DISPLAY syn.`con (InR _ _ , t , refl)           = `i₂ t       #-}
{-# DISPLAY syn.`con (Cas _ _ _ , t , l , r , refl) = `case t l r #-}

-- The Typed Reduction relation can be defined in the usual fashion
-- thanks to the pattern synonyms introduced above. Its reflexive
-- transitive closure is obtained by instantiating the standard
-- library's Star.

infix 3 _⊢_∋_↝_ _⊢_∋_↝⋆_
data _⊢_∋_↝_ Γ : ∀ τ → Term τ Γ → Term τ Γ → Set where
-- computational
  β    : ∀ {σ τ} t (u : Term σ Γ) → Γ ⊢ τ ∋ `λ t `∙ u ↝ t [ u /0]
  ι₁   : ∀ {σ τ ν} (t : Term σ Γ) l (r : Term ν (τ ∷ Γ)) → Γ ⊢ ν ∋ `case (`i₁ t) l r ↝ l [ t /0]
  ι₂   : ∀ {σ τ ν} (t : Term τ Γ) (l : Term ν (σ ∷ Γ)) r → Γ ⊢ ν ∋ `case (`i₂ t) l r ↝ r [ t /0]
-- structural
  [λ]  : ∀ {σ τ t u} → (σ ∷ Γ) ⊢ τ ∋ t ↝ u → Γ ⊢ σ ⇒ τ ∋ `λ t ↝ `λ u
  [∙]₁ : ∀ {σ τ t u} f → Γ ⊢ σ ∋ t ↝ u → Γ ⊢ τ ∋ f `∙ t ↝ f `∙ u
  [∙]₂ : ∀ {σ τ f g} → Γ ⊢ σ ⇒ τ ∋ f ↝ g → ∀ t → Γ ⊢ τ ∋ f `∙ t ↝ g `∙ t
  [i₁] : ∀ {σ τ t u} → Γ ⊢ σ ∋ t ↝ u → Γ ⊢ σ + τ ∋ `i₁ t ↝ `i₁ u
  [i₂] : ∀ {σ τ t u} → Γ ⊢ τ ∋ t ↝ u → Γ ⊢ σ + τ ∋ `i₂ t ↝ `i₂ u
  [c]₁ : ∀ {σ τ ν t u} → Γ ⊢ σ + τ ∋ t ↝ u → ∀ l r → Γ ⊢ ν ∋ `case t l r ↝ `case u l r
  [c]₂ : ∀ {σ τ ν l m} → ∀ t → σ ∷ Γ ⊢ ν ∋ l ↝ m → (r : Term ν (τ ∷ Γ)) → Γ ⊢ ν ∋ `case t l r ↝ `case t m r
  [c]₃ : ∀ {σ τ ν r s} → ∀ t → (l : Term ν (σ ∷ Γ)) → τ ∷ Γ ⊢ ν ∋ r ↝ s → Γ ⊢ ν ∋ `case t l r ↝ `case t l s

_⊢_∋_↝⋆_ : ∀ Γ σ → Term σ Γ → Term σ Γ → Set
Γ ⊢ σ ∋ t ↝⋆ u = Star (Γ ⊢ σ ∋_↝_) t u

-- Lemma 1.2
-- Stability of Reduction under thinning and substitution
-- (Stability of Typing is a consequence of Term being a typed syntax)

th^↝ : ∀ {σ Γ Δ t u} ρ → Γ ⊢ σ ∋ t ↝ u → Δ ⊢ σ ∋ ren ρ t ↝ ren ρ u
th^↝ ρ (β t u)      = subst (_ ⊢ _ ∋ ren ρ (`λ t `∙ u) ↝_) (sym $ renβ TermD t u ρ) (β _ _)
th^↝ ρ (ι₁ t l r)   = subst (_ ⊢ _ ∋ ren ρ (`case (`i₁ t) l r) ↝_) (sym $ renβ TermD l t ρ) (ι₁ _ _ _)
th^↝ ρ (ι₂ t l r)   = subst (_ ⊢ _ ∋ ren ρ (`case (`i₂ t) l r) ↝_) (sym $ renβ TermD r t ρ) (ι₂ _ _ _)
th^↝ ρ ([λ] r)      = [λ] (th^↝ _ r)
th^↝ ρ ([∙]₁ f r)   = [∙]₁ (ren ρ f) (th^↝ ρ r)
th^↝ ρ ([∙]₂ r t)   = [∙]₂ (th^↝ ρ r) (ren ρ t)
th^↝ ρ ([i₁] c)     = [i₁] (th^↝ ρ c)
th^↝ ρ ([i₂] c)     = [i₂] (th^↝ ρ c)
th^↝ ρ ([c]₁ c l r) = [c]₁ (th^↝ ρ c) (ren _ l) (ren _ r)
th^↝ ρ ([c]₂ t c r) = [c]₂ (ren ρ t) (th^↝ _ c) (ren _ r)
th^↝ ρ ([c]₃ t l c) = [c]₃ (ren ρ t) (ren _ l) (th^↝ _ c)

-- Lemma 1.3
sub^↝ : ∀ {σ Γ Δ t u} ρ → Γ ⊢ σ ∋ t ↝ u → Δ ⊢ σ ∋ sub ρ t ↝ sub ρ u
sub^↝ ρ (β t u)      = subst (_ ⊢ _ ∋ sub ρ (`λ t `∙ u) ↝_) (sym $ subβ TermD t u ρ) (β _ _)
sub^↝ ρ (ι₁ t l r)   = subst (_ ⊢ _ ∋ sub ρ (`case (`i₁ t) l r) ↝_) (sym $ subβ TermD l t ρ) (ι₁ _ _ _)
sub^↝ ρ (ι₂ t l r)   = subst (_ ⊢ _ ∋ sub ρ (`case (`i₂ t) l r) ↝_) (sym $ subβ TermD r t ρ) (ι₂ _ _ _)
sub^↝ ρ ([λ] r)      = [λ] (sub^↝ _ r)
sub^↝ ρ ([∙]₁ f r)   = [∙]₁ (sub ρ f) (sub^↝ ρ r)
sub^↝ ρ ([∙]₂ r t)   = [∙]₂ (sub^↝ ρ r) (sub ρ t)
sub^↝ ρ ([i₁] c)     = [i₁] (sub^↝ ρ c)
sub^↝ ρ ([i₂] c)     = [i₂] (sub^↝ ρ c)
sub^↝ ρ ([c]₁ c l r) = [c]₁ (sub^↝ ρ c) (sub _ l) (sub _ r)
sub^↝ ρ ([c]₂ t c r) = [c]₂ (sub ρ t) (sub^↝ _ c) (sub _ r)
sub^↝ ρ ([c]₃ t l c) = [c]₃ (sub ρ t) (sub _ l) (sub^↝ _ c)

[/0]^↝ : ∀ {σ τ Γ b b′} → (σ ∷ Γ) ⊢ τ ∋ b ↝ b′ → ∀ u → Γ ⊢ τ ∋ b [ u /0] ↝ b′ [ u /0]
[/0]^↝ r u = sub^↝ (u /0]) r

-- Lemma 1.4
↝⋆^R : Rel Term Term
rel ↝⋆^R = _ ⊢ _ ∋_↝⋆_

[v↦t↝⋆t] : ∀ {Γ Δ} {ρ : (Γ ─Env) Term Δ} → rel.∀[ ↝⋆^R ] ρ ρ
lookup^R [v↦t↝⋆t] k = S.ε

-- 1., 2., 3., 4.: cf. Star's gmap
-- 5.
sub^↝⋆ : ∀ {σ Γ Δ} (t : Term σ Γ) {ρ ρ′} →
         rel.∀[ ↝⋆^R ] ρ ρ′ → Δ ⊢ σ ∋ sub ρ t ↝⋆ sub ρ′ t
sub^↝⋆ t ρ^R = Sim.sim sim ρ^R t where

  sim : Sim ↝⋆^R ↝⋆^R TermD Substitution Substitution
  Sim.th^R  sim = λ ρ → S.gmap _ (th^↝ ρ)
  Sim.var^R sim = id
  Sim.alg^R sim = λ where
    (f `∙' t) {ρ₁} {ρ₂} ρ^R (refl , f^R , t^R , _) → S.gmap _ (λ f → [∙]₂ f (sub ρ₁ t)) f^R
                                                S.◅◅ S.gmap _ ([∙]₁ (sub ρ₂ f)) t^R
    (`λ' b) ρ^R (refl , b^R , _) → S.gmap `λ [λ] (b^R _ [v↦t↝⋆t])
    (`i₁' t) ρ^R (refl , t^R , _) → S.gmap `i₁ [i₁] t^R
    (`i₂' t) ρ^R (refl , t^R , _) → S.gmap `i₂ [i₂] t^R
    (`case' t l r) {ρ₁} {ρ₂} ρ^R (refl , t^R , l^R , r^R , _) →
      S.gmap _ (λ c → [c]₁ c (sub _ l) (sub _ r)) t^R
      S.◅◅ S.gmap _ (λ c → [c]₂ (sub ρ₂ t) c (sub _ r)) (l^R _ [v↦t↝⋆t])
      S.◅◅ S.gmap  _ ([c]₃ (sub ρ₂ t) (sub _ l)) (r^R _  [v↦t↝⋆t])

[/0]^↝⋆ : ∀ {σ τ Γ} t {u u′} → Γ ⊢ σ ∋ u ↝ u′ → Γ ⊢ τ ∋ t [ u /0] ↝⋆ t [ u′ /0]
[/0]^↝⋆ t r = sub^↝⋆ t ([v↦t↝⋆t] ∙^R S.return r)

-- Inversion lemmas for the interaction between ren, ∙, λ and ↝

th⁻¹^`∙ : ∀ {σ τ Γ Δ} (u : Term τ Γ) {f : Term (σ ⇒ τ) Δ} {t} ρ → f `∙ t ≡ ren ρ u →
          ∃ λ f′ → ∃ λ t′ → f′ `∙ t′ ≡ u × f ≡ ren ρ f′ × t ≡ ren ρ t′
th⁻¹^`∙ (f′ `∙ t′)     ρ refl = f′ , t′ , refl , refl , refl
th⁻¹^`∙ (`var _)       ρ ()
th⁻¹^`∙ (`λ _)         ρ ()
th⁻¹^`∙ (`i₁ _)        ρ ()
th⁻¹^`∙ (`i₂ _)        ρ ()
th⁻¹^`∙ (`case _ _ _)  ρ ()

th⁻¹^`λ : ∀ {σ τ Γ Δ} (u : Term (σ ⇒ τ) Γ) {b : Term τ (σ ∷ Δ)} ρ → `λ b ≡ ren ρ u →
          ∃ λ b′ → `λ b′ ≡ u × b ≡ ren (lift vl^Var (σ ∷ []) ρ) b′
th⁻¹^`λ (`λ b′)        ρ refl = b′ , refl , refl
th⁻¹^`λ (`var v)                  ρ ()
th⁻¹^`λ (_ `∙ _)                  ρ ()
th⁻¹^`λ (`case _ _ _)             ρ ()
th⁻¹^`λ (`con (InL _ _ , _ , ())) ρ eq
th⁻¹^`λ (`con (InR _ _ , _ , ())) ρ eq

th⁻¹^↝ : ∀ {σ Γ Δ u′} t ρ → Δ ⊢ σ ∋ ren ρ t ↝ u′ →
          ∃ λ u → u′ ≡ ren ρ u × Γ ⊢ σ ∋ t ↝ u
th⁻¹^↝ (`var v) ρ ()
th⁻¹^↝ (`λ b `∙ t) ρ (β _ _) = b [ t /0] , sym (renβ TermD b t ρ) , β b t
th⁻¹^↝ (`λ t)      ρ ([λ] r) =
  let (t′ , eq , r′) = th⁻¹^↝ t _ r in `λ t′ , cong `λ eq , [λ] r′
th⁻¹^↝ (f `∙ t) ρ ([∙]₁ ._ r) =
  let (t′ , eq , r′) = th⁻¹^↝ t ρ r in f `∙ t′ , cong (ren ρ f `∙_) eq , [∙]₁ _ r′
th⁻¹^↝ (f `∙ t) ρ ([∙]₂ r ._) =
  let (f′ , eq , r′) = th⁻¹^↝ f ρ r in f′ `∙ t , cong (_`∙ ren ρ t) eq , [∙]₂ r′ _
th⁻¹^↝ (`i₁ t) ρ ([i₁] r) =
  let (t′ , eq , r′) = th⁻¹^↝ t ρ r in (`i₁ t′ , cong `i₁ eq , [i₁] r′)
th⁻¹^↝ (`i₂ t) ρ ([i₂] r) =
  let (t′ , eq , r′) = th⁻¹^↝ t ρ r in (`i₂ t′ , cong `i₂ eq , [i₂] r′)
th⁻¹^↝ (`case (`i₁ t) b₁ b₂) ρ (ι₁ _ _ _) = b₁ [ t /0] , sym (renβ TermD b₁ t ρ) , ι₁ t b₁ b₂
th⁻¹^↝ (`case (`i₂ t) b₁ b₂) ρ (ι₂ _ _ _) = b₂ [ t /0] , sym (renβ TermD b₂ t ρ) , ι₂ t b₁ b₂
th⁻¹^↝ (`case t b₁ b₂) ρ ([c]₁ r _ _) = let (t′ , eq , r′) = th⁻¹^↝ t ρ r in
  (`case t′ b₁ b₂ , cong (λ r → `case r (ren _ b₁) (ren _ b₂)) eq , [c]₁ r′ b₁ b₂)
th⁻¹^↝ (`case t b₁ b₂) ρ ([c]₂ _ r _) = let (b₁′ , eq , r′) = th⁻¹^↝ b₁ _ r in
  (`case t b₁′ b₂ , cong (λ r → `case (ren ρ t) r (ren _ b₂)) eq , [c]₂ t r′ b₂)
th⁻¹^↝ (`case t b₁ b₂) ρ ([c]₃ _ _ r) = let (b₂′ , eq , r′) = th⁻¹^↝ b₂ _ r in
  (`case t b₁ b₂′ , cong (`case (ren ρ t) (ren _ b₁)) eq , [c]₃ t b₁ r′)

th⁻¹^↝⋆ : ∀ {σ Γ Δ u′} t ρ → Δ ⊢ σ ∋ ren ρ t ↝⋆ u′ →
          ∃ λ u → u′ ≡ ren ρ u × Γ ⊢ σ ∋ t ↝⋆ u
th⁻¹^↝⋆ {σ} t ρ rs = go t ρ refl rs where

  go : ∀ {Γ Δ} t ρ → ∀ {t′ u′} → t′ ≡ ren ρ t → Δ ⊢ σ ∋ t′ ↝⋆ u′ →
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

Closed : ∀ {σ Γ} → (Term σ Γ → Term σ Γ → Set) →
         (Term σ Γ → Set) → Term σ Γ → Set
Closed red R t = ∀ {u} → red t u → R u

Closed⇒Closed⋆ : ∀ {σ Γ red R} → (∀ {t : Term σ Γ} → R t → Closed red R t) →
                 ∀ {t} → R t → Closed (Star red) R t
Closed⇒Closed⋆ cl t^R Star.ε        = t^R
Closed⇒Closed⋆ cl t^R (r Star.◅ rs) = Closed⇒Closed⋆ cl (cl t^R r) rs

-- Definition 3.1
infix 3 _⊢sn_∋_<_ _⊢sn_∋_
data _⊢sn_∋_<_ Γ σ (t : Term σ Γ) : Size → Set where
  sn : ∀ {i} → Closed (Γ ⊢ σ ∋_↝_) (Γ ⊢sn σ ∋_< i) t → Γ ⊢sn σ ∋ t < ↑ i

_⊢sn_∋_ = _⊢sn_∋_< _

Closed-sn : ∀ {σ Γ t} → Γ ⊢sn σ ∋ t → Closed (Γ ⊢ σ ∋_↝_) (Γ ⊢sn σ ∋_) t
Closed-sn (sn t^SN) = t^SN

-- Lemma 4.1 Closure of sn under ↝⋆
Closed⋆-sn : ∀ {σ Γ t} → Γ ⊢sn σ ∋ t → Closed (Γ ⊢ σ ∋_↝⋆_) (Γ ⊢sn σ ∋_) t
Closed⋆-sn = Closed⇒Closed⋆ Closed-sn

-- Lemma 4.2 Weakening of strongly normalizing terms
th^sn : ∀ {σ Γ Δ t} ρ → Γ ⊢sn σ ∋ t → Δ ⊢sn σ ∋ ren ρ t
th^sn ρ (sn t^SN) = sn $ λ r →
  let (_ , eq , r′) = th⁻¹^↝ _ ρ r
  in subst (_ ⊢sn _ ∋_) (sym eq) $ th^sn ρ (t^SN r′)

-- Lemma 4.3 Anti-renaming (Strengthening) of strongly normalizing terms
th⁻¹^sn : ∀ {σ Γ Δ t} ρ → Δ ⊢sn σ ∋ ren ρ t → Γ ⊢sn σ ∋ t
th⁻¹^sn ρ (sn tρ^sn) = sn (λ r → th⁻¹^sn ρ (tρ^sn (th^↝ ρ r)))

-- Lemma 4.4 Properties of strongly normalizing terms

-- 1.
sub⁻¹^sn : ∀ {σ Γ Δ} t ρ → Δ ⊢sn σ ∋ (sub ρ t) → Γ ⊢sn σ ∋ t
sub⁻¹^sn t ρ (sn tρ^sn) = sn (λ r → sub⁻¹^sn _ ρ (tρ^sn (sub^↝ ρ r)))

[/0]⁻¹^sn : ∀ {σ τ Γ} t u → Γ ⊢sn τ ∋ (t [ u /0]) → (σ ∷ Γ) ⊢sn τ ∋ t
[/0]⁻¹^sn t u t[u]^sn = sub⁻¹^sn t (u /0]) t[u]^sn

-- 2.
`λ^sn : ∀ {σ τ Γ t} → (σ ∷ Γ) ⊢sn τ ∋ t → Γ ⊢sn σ ⇒ τ ∋ `λ t
`λ^sn (sn t^R) = sn λ { ([λ] r) → `λ^sn (t^R r) }

`i₁^sn : ∀ {σ τ Γ t} → Γ ⊢sn σ ∋ t → Γ ⊢sn σ + τ ∋ `i₁ t
`i₁^sn (sn t^R) = sn λ { ([i₁] r) → `i₁^sn (t^R r) }

`i₂^sn : ∀ {σ τ Γ t} → Γ ⊢sn τ ∋ t → Γ ⊢sn σ + τ ∋ `i₂ t
`i₂^sn (sn t^R) = sn λ { ([i₂] r) → `i₂^sn (t^R r) }

-- 3.
`∙t⁻¹^sn : ∀ {σ τ Γ f t i} → Γ ⊢sn τ ∋ (f `∙ t) < i → Γ ⊢sn σ ⇒ τ ∋ f < i
`∙t⁻¹^sn (sn ft^sn) = sn (λ r → `∙t⁻¹^sn (ft^sn ([∙]₂ r _)))

f`∙⁻¹^sn : ∀ {σ τ Γ f t i} → Γ ⊢sn τ ∋ (f `∙ t) < i → Γ ⊢sn σ ∋ t < i
f`∙⁻¹^sn (sn ft^sn) = sn (λ r → f`∙⁻¹^sn (ft^sn ([∙]₁ _ r)))

`∙⁻¹^sn : ∀ {σ τ Γ f t i} → Γ ⊢sn τ ∋ (f `∙ t) < i → Γ ⊢sn σ ⇒ τ ∋ f < i × Γ ⊢sn σ ∋ t < i
`∙⁻¹^sn ft^sn = `∙t⁻¹^sn ft^sn , f`∙⁻¹^sn ft^sn

-- 4.
`λ⁻¹^sn : ∀ {σ τ Γ t i} → Γ ⊢sn σ ⇒ τ ∋ `λ t < i → (σ ∷ Γ) ⊢sn τ ∋ t < i
`λ⁻¹^sn (sn λt^sn) = sn (λ r → `λ⁻¹^sn (λt^sn ([λ] r)))

-- 5.
`i₁⁻¹^sn : ∀ {σ τ Γ t i} → Γ ⊢sn σ + τ ∋ `i₁ t < i → Γ ⊢sn σ ∋ t < i
`i₁⁻¹^sn (sn i₁t^sn) = sn (λ r → `i₁⁻¹^sn (i₁t^sn ([i₁] r)))

`i₂⁻¹^sn : ∀ {σ τ Γ t i} → Γ ⊢sn σ + τ ∋ `i₂ t < i → Γ ⊢sn τ ∋ t < i
`i₂⁻¹^sn (sn i₂t^sn) = sn (λ r → `i₂⁻¹^sn (i₂t^sn ([i₂] r)))

-- 6.
`case₁⁻¹^sn : ∀ {σ τ ν Γ t l r i} → Γ ⊢sn ν ∋ `case t l r < i → Γ ⊢sn σ + τ ∋ t < i
`case₁⁻¹^sn (sn c^sn) = sn (λ r → `case₁⁻¹^sn (c^sn ([c]₁ r _ _)))

`case₂⁻¹^sn : ∀ {σ τ ν Γ t l i} {r : Term ν (τ ∷ Γ)} → Γ ⊢sn ν ∋ `case t l r < i → (σ ∷ Γ) ⊢sn ν ∋ l < i
`case₂⁻¹^sn (sn c^sn) = sn (λ r → `case₂⁻¹^sn (c^sn ([c]₂ _ r _)))

`case₃⁻¹^sn : ∀ {σ τ ν Γ t r i} {l : Term ν (σ ∷ Γ)} → Γ ⊢sn ν ∋ `case t l r < i → (τ ∷ Γ) ⊢sn ν ∋ r < i
`case₃⁻¹^sn (sn c^sn) = sn (λ r → `case₃⁻¹^sn (c^sn ([c]₃ _ _ r)))

`case⁻¹^sn : ∀ {σ τ ν Γ t l r i} → Γ ⊢sn ν ∋ `case t l r < i →
  Γ ⊢sn σ + τ ∋ t < i × (σ ∷ Γ) ⊢sn ν ∋ l < i × (τ ∷ Γ) ⊢sn ν ∋ r < i
`case⁻¹^sn c^sn = `case₁⁻¹^sn c^sn , `case₂⁻¹^sn c^sn , `case₃⁻¹^sn c^sn

-- Evaluation contexts indexed by the Scope, the type of the hole, and the
-- type of the overall expression.

infix 3 _∣_⊢_ _∣_⊢sn_∋_
data _∣_⊢_ Γ α : Type → Set where
  <>  : Γ ∣ α ⊢ α
  app : ∀ {σ τ} → Γ ∣ α ⊢ σ ⇒ τ → Term σ Γ → Γ ∣ α ⊢ τ
  cas : ∀ {σ τ ν} → Γ ∣ α ⊢ σ + τ → Term ν (σ ∷ Γ) → Term ν (τ ∷ Γ) → Γ ∣ α ⊢ ν

data _∣_⊢sn_∋_ Γ α : ∀ τ (c : Γ ∣ α ⊢ τ) → Set where
  <>  : Γ ∣ α ⊢sn α ∋ <>
  app : ∀ {σ τ c t} → Γ ∣ α ⊢sn σ ⇒ τ ∋ c → Γ ⊢sn σ ∋ t → Γ ∣ α ⊢sn τ ∋ app c t
  cas : ∀ {σ τ ν c l r} → Γ ∣ α ⊢sn σ + τ ∋ c →
        (σ ∷ Γ) ⊢sn ν ∋ l → (τ ∷ Γ) ⊢sn ν ∋ r → Γ ∣ α ⊢sn ν ∋ cas c l r

cut : ∀ {Γ α σ} → Term α Γ → Γ ∣ α ⊢ σ → Term σ Γ
cut t <>          = t
cut t (app c u)   = cut t c `∙ u
cut t (cas c l r) = `case (cut t c) l r

-- Lemma 4.5 Multi-step Reductions with Evaluation Contexts
cut^↝ : ∀ {Γ α σ t u} c → Γ ⊢ α ∋ t ↝ u → Γ ⊢ σ ∋ cut t c ↝ cut u c
cut^↝ <>          red = red
cut^↝ (app c t)   red = [∙]₂ (cut^↝ c red) t
cut^↝ (cas c l r) red = [c]₁ (cut^↝ c red) l r

cut^↝⋆ : ∀ {Γ α σ t u} c → Γ ⊢ α ∋ t ↝⋆ u → Γ ⊢ σ ∋ cut t c ↝⋆ cut u c
cut^↝⋆ c = S.gmap (flip cut c) (cut^↝ c)

-- Lemma 4.6 Evaluation Contexts
-- Neutrality in the sense of Girard: not (value constructor)-headed
data Neutral {Γ σ} : Term σ Γ → Set where
  var : ∀ v → Neutral (`var v)
  app : ∀ {τ} f (t : Term τ Γ) → Neutral (f `∙ t)
  cas : ∀ {σ τ} (t : Term (σ + τ) Γ) l r → Neutral (`case t l r)

cut⁻¹‿sn^↝ : ∀ {Γ α σ u c t} → Γ ∣ α ⊢sn σ ∋ c → Neutral t → Γ ⊢ σ ∋ cut t c ↝ u →
               (∃ λ t′ → u ≡ cut t′ c × Γ ⊢ α ∋ t ↝ t′)
             ⊎ (∃ λ c′ → u ≡ cut t c′ × Γ ∣ α ⊢sn σ ∋ c′
               × ∀ t′ → Γ ⊢ σ ∋ cut t′ c ↝ cut t′ c′)
-- reduction in the plugged subterm
cut⁻¹‿sn^↝ <> ne r = inj₁ (_ , refl , r)
-- no redexes at the interface thanks to Girard neutrality
cut⁻¹‿sn^↝ (app <> t^sn)      () (β b t)
cut⁻¹‿sn^↝ (cas <> l^sn r^sn) () (ι₁ t l r)
cut⁻¹‿sn^↝ (cas <> l^sn r^sn) () (ι₂ t l r)
-- reduction in the context
cut⁻¹‿sn^↝ (app c^sn t^sn) ne ([∙]₁ _ r) =
  inj₂ (_ , refl , app c^sn (Closed-sn t^sn r) , λ u → [∙]₁ _ r)
cut⁻¹‿sn^↝ (cas c^sn l^sn r^sn) ne ([c]₂ t red r) =
  inj₂ (cas _ _ r , refl , cas c^sn (Closed-sn l^sn red) r^sn , λ u → [c]₂ _ red r)
cut⁻¹‿sn^↝ (cas c^sn l^sn r^sn) ne ([c]₃ t l red) =
  inj₂ (cas _ l _ , refl , cas c^sn l^sn (Closed-sn r^sn red) , λ u → [c]₃ _ l red)
-- structural cases: reduction happens deeper
cut⁻¹‿sn^↝ (app c^sn t^sn) ne ([∙]₂ r t) with cut⁻¹‿sn^↝ c^sn ne r
... | inj₁ (t′ , eq , r′)         = inj₁ (t′ , cong (_`∙ t) eq , r′)
... | inj₂ (c′ , eq , c′^sn , r′) =
  inj₂ (app c′ t , cong (_`∙ t) eq , app c′^sn t^sn , λ u → [∙]₂ (r′ u) t)
cut⁻¹‿sn^↝ (cas c^sn l^sn r^sn) ne ([c]₁ red l r) with cut⁻¹‿sn^↝ c^sn ne red
... | inj₁ (t′ , eq , r′)         = inj₁ (t′ , cong (λ t → `case t l r) eq , r′)
... | inj₂ (c′ , eq , c′^sn , r′) =
  inj₂ (_ , cong (λ t → `case t l r) eq , cas c′^sn l^sn r^sn , λ u → [c]₁ (r′ u) l r)

cut⁻¹^↝ : ∀ {Γ α σ u} c {v : Var α Γ} → Γ ⊢ σ ∋ cut (`var v) c ↝ u →
          ∃ λ c′ → u ≡ cut (`var v) c′
cut⁻¹^↝ (app <> t)   ([∙]₁ _ r)   = app <> _ , refl
cut⁻¹^↝ (app c t)    ([∙]₁ _ r)   = app c _ , refl
cut⁻¹^↝ (app c t)    ([∙]₂ r .t)  =
  let (c′ , eq) = cut⁻¹^↝ c r in app c′ _ , cong (_`∙ _) eq
cut⁻¹^↝ (cas <> l r) ([c]₂ _ _ _) = cas <> _ _ , refl
cut⁻¹^↝ (cas <> l r) ([c]₃ _ _ _) = cas <> _ _ , refl
cut⁻¹^↝ (cas c _ _)  ([c]₁ r _ _) =
  let (c′ , eq) = cut⁻¹^↝ c r in cas c′ _ _ , cong (λ c → `case c _ _) eq
cut⁻¹^↝ (cas c l r)  ([c]₂ _ _ _) = cas c _ _ , refl
cut⁻¹^↝ (cas c l r)  ([c]₃ _ _ _) = cas c _ _ , refl
cut⁻¹^↝ <>           ()

cut⁻¹^sn : ∀ {Γ α σ} t c → Γ ⊢sn σ ∋ cut t c → (Γ ∣ α ⊢sn σ ∋ c) × (Γ ⊢sn α ∋ t)
cut⁻¹^sn t <>        t^sn     = <> , t^sn
cut⁻¹^sn t (app c u) c[t]u^sn =
  let (c[t]^sn , u^sn) = `∙⁻¹^sn c[t]u^sn in
  let (c^sn , t^sn) = cut⁻¹^sn t c c[t]^sn in app c^sn u^sn , t^sn
cut⁻¹^sn t (cas c l r) c[t]lr^sn =
  let (c[t]^sn , l^sn , r^sn) = `case⁻¹^sn c[t]lr^sn in
  let (c^sn , t^sn) = cut⁻¹^sn t c c[t]^sn in cas c^sn l^sn r^sn , t^sn

-- Lemma 4.7 Closure properties of neutral terms
-- 1.
`var^sne : ∀ {σ Γ} v → Γ ⊢sn σ ∋ `var v
`var^sne v = sn (λ ())

-- 2.
`∙^sne : ∀ {Γ α σ τ t} {v : Var α Γ} c → Γ ⊢sn σ ⇒ τ ∋ cut (`var v) c → Γ ⊢sn σ ∋ t →
         Γ ⊢sn τ ∋ cut (`var v) (app c t)
`∙^sne c f^sne t^sn = sn (go c f^sne t^sn) where

  go : ∀ {Γ α σ τ t} {v : Var α Γ} c → Γ ⊢sn σ ⇒ τ ∋ cut (`var v) c → Γ ⊢sn σ ∋ t →
       Closed (Γ ⊢ τ ∋_↝_) (Γ ⊢sn τ ∋_) (cut (`var v) (app c t))
  go <>        f^sne      t^sn      ([∙]₂ () t)
  go c         f^sne      (sn t^sn) ([∙]₁ _ r) = sn (go c f^sne (t^sn r))
  go c         (sn f^sne) t^sn      ([∙]₂ r t) =
    let (c′ , eq) = cut⁻¹^↝ c r in let r′ = subst (_ ⊢ _ ∋ _ ↝_) eq r in
    subst (λ g → _ ⊢sn _ ∋ g `∙ t) (sym eq) (sn (go c′ (f^sne r′) t^sn))

-- 3.
`case^sne : ∀ {Γ α σ τ ν l r} {v : Var α Γ} c → Γ ⊢sn σ + τ ∋ cut (`var v) c →
  (σ ∷ Γ) ⊢sn ν ∋ l → (τ ∷ Γ) ⊢sn ν ∋ r → Γ ⊢sn ν ∋ cut (`var v) (cas c l r)
`case^sne c s^sn l^sn r^sn = sn (go c s^sn l^sn r^sn) where

  go : ∀ {Γ α σ τ ν l r} {v : Var α Γ} c → Γ ⊢sn σ + τ ∋ cut (`var v) c →
      (σ ∷ Γ) ⊢sn ν ∋ l → (τ ∷ Γ) ⊢sn ν ∋ r → Closed (Γ ⊢ ν ∋_↝_) (Γ ⊢sn ν ∋_) (cut (`var v) (cas c l r))
  go <> s^sne      l^sn      r^sn      ([c]₁ () _ _)
  go c  s^sne      (sn l^sn) r^sn      ([c]₂ _ red _) = sn (go c s^sne (l^sn red) r^sn)
  go c  s^sne      l^sn      (sn r^sn) ([c]₃ _ _ red) = sn (go c s^sne l^sn (r^sn red))
  go c  (sn s^sne) l^sn      r^sn      ([c]₁ red l r) =
    let (c′ , eq) = cut⁻¹^↝ c red in let red′ = subst (_ ⊢ _ ∋ _ ↝_) eq red in
    subst (λ g → _ ⊢sn _ ∋ `case g l r) (sym eq) (sn (go c′ (s^sne red′) l^sn r^sn))

cut^sn : ∀ {Γ α σ} v {c} → Γ ∣ α ⊢sn σ ∋ c → Γ ⊢sn σ ∋ cut (`var v) c
cut^sn v             <>                   = `var^sne v
cut^sn v {app c t}   (app c^sn t^sn)      = `∙^sne c (cut^sn v c^sn) t^sn
cut^sn v {cas c l r} (cas c^sn l^sn r^sn) = `case^sne c (cut^sn v c^sn) l^sn r^sn

-- Lemma 4.8 Composition of evaluation contexts
_∘C_ : ∀ {Γ α β σ} → Γ ∣ β ⊢ σ → Γ ∣ α ⊢ β → Γ ∣ α ⊢ σ
<>        ∘C c′ = c′
app c t   ∘C c′ = app (c ∘C c′) t
cas c l r ∘C c′ = cas (c ∘C c′) l r

cut-∘C : ∀ {Γ α β σ} t (c : Γ ∣ β ⊢ σ) (c′ : Γ ∣ α ⊢ β) →
         cut (cut t c′) c ≡ cut t (c ∘C c′)
cut-∘C t <>          c′ = refl
cut-∘C t (app c u)   c′ = cong (_`∙ u) (cut-∘C t c c′)
cut-∘C t (cas c l r) c′ = cong (λ t → `case t l r) (cut-∘C t c c′)

∘C^sn : ∀ {Γ α β σ c c′} → Γ ∣ β ⊢sn σ ∋ c → Γ ∣ α ⊢sn β ∋ c′ → Γ ∣ α ⊢sn σ ∋ c ∘C c′
∘C^sn <>                   c′^sn = c′^sn
∘C^sn (app c^sn t^sn)      c′^sn = app (∘C^sn c^sn c′^sn) t^sn
∘C^sn (cas c^sn l^sn r^sn) c′^sn = cas (∘C^sn c^sn c′^sn) l^sn r^sn

-- Lemma 4.9
-- 1.
β⁻¹^Closed-sn : ∀ {Γ α σ τ} c b u → (σ ∷ Γ) ⊢sn α ∋ b → Γ ⊢sn σ ∋ u →
                Γ ⊢sn τ ∋ cut (b [ u /0]) c → Γ ∣ α ⊢sn τ ∋ c →
                Closed (Γ ⊢ τ ∋_↝_) (Γ ⊢sn τ ∋_) (cut (`λ b `∙ u) c)
β⁻¹^Closed-sn c b u b^sn@(sn b^sn′) u^sn@(sn u^sn′) c[b[u]]^sn@(sn c[b[u]]^sn′) c^sn r
  with cut⁻¹‿sn^↝ c^sn (app (`λ b) u) r
... | inj₁ (._ , refl , β .b .u)          = c[b[u]]^sn
... | inj₁ (._ , refl , [∙]₁ _ r′)  =
  let c[b[u]]^sn′ = Closed⋆-sn c[b[u]]^sn (cut^↝⋆ c ([/0]^↝⋆ b r′)) in
  sn (β⁻¹^Closed-sn c b _ b^sn (u^sn′ r′) c[b[u]]^sn′ c^sn)
... | inj₁ (._ , refl , [∙]₂ ([λ] r′) .u) =
  sn (β⁻¹^Closed-sn c _ u (b^sn′ r′) u^sn (c[b[u]]^sn′ (cut^↝ c ([/0]^↝ r′ u))) c^sn)
... | inj₂ (c′ , refl , c′^sn , r′) =
  sn (β⁻¹^Closed-sn c′ b u b^sn u^sn (c[b[u]]^sn′ (r′ (b [ u /0]))) c′^sn)

β⁻¹^sn : ∀ {Γ α σ τ b u c} → (σ ∷ Γ) ⊢sn α ∋ b → Γ ⊢sn σ ∋ u →
         Γ ⊢sn τ ∋ cut (b [ u /0]) c → Γ ∣ α ⊢sn τ ∋ c →
         Γ ⊢sn τ ∋ cut (`λ b `∙ u) c
β⁻¹^sn b^sn u^sn c[b[u]]^sn c^sn = sn (β⁻¹^Closed-sn _ _ _ b^sn u^sn c[b[u]]^sn c^sn)

-- 2.
ι₁⁻¹^Closed-sn : ∀ {Γ α σ τ ν} c t l r → Γ ⊢sn σ ∋ t → (σ ∷ Γ) ⊢sn α ∋ l → (τ ∷ Γ) ⊢sn α ∋ r →
  Γ ⊢sn ν ∋ cut (l [ t /0]) c → Γ ∣ α ⊢sn ν ∋ c →
  Closed (Γ ⊢ ν ∋_↝_) (Γ ⊢sn ν ∋_) (cut (`case (`i₁ t) l r) c)
ι₁⁻¹^Closed-sn c t l r t^sn@(sn t^sn′) l^sn@(sn l^sn′) r^sn@(sn r^sn′) c[l[t]]^sn@(sn c[l[t]]^sn′) c^sn red
  with cut⁻¹‿sn^↝ c^sn (cas (`i₁ t) l r) red
... | inj₁ (._ , refl , ι₁ .t .l .r)            = c[l[t]]^sn
... | inj₁ (._ , refl , [c]₁ ([i₁] red′) .l .r) =
  let c[l[t]]^sn′ = Closed⋆-sn c[l[t]]^sn (cut^↝⋆ c ([/0]^↝⋆ l red′)) in
  sn (ι₁⁻¹^Closed-sn c _ l r (t^sn′ red′) l^sn r^sn c[l[t]]^sn′ c^sn)
... | inj₁ (._ , refl , [c]₂ _ red′ .r)         =
  sn (ι₁⁻¹^Closed-sn c t _ r t^sn (l^sn′ red′) r^sn (c[l[t]]^sn′ (cut^↝ c ([/0]^↝ red′ t))) c^sn)
... | inj₁ (._ , refl , [c]₃ _ .l red′)         =
  sn (ι₁⁻¹^Closed-sn c t l _ t^sn l^sn (r^sn′ red′) c[l[t]]^sn c^sn)
... | inj₂ (c′ , refl , c′^sn , red′) =
  sn (ι₁⁻¹^Closed-sn c′ t l r t^sn l^sn r^sn (c[l[t]]^sn′ (red′ (l [ t /0]))) c′^sn)

ι₁⁻¹^sn : ∀ {Γ α σ τ ν} c t l r → Γ ⊢sn σ ∋ t → (σ ∷ Γ) ⊢sn α ∋ l → (τ ∷ Γ) ⊢sn α ∋ r →
  Γ ⊢sn ν ∋ cut (l [ t /0]) c → Γ ∣ α ⊢sn ν ∋ c → Γ ⊢sn ν ∋ cut (`case (`i₁ t) l r) c
ι₁⁻¹^sn c t l r t^sn l^sn r^sn c[l[t]]^sn c^sn =
  sn (ι₁⁻¹^Closed-sn c t l r t^sn l^sn r^sn c[l[t]]^sn c^sn)

-- 3.
ι₂⁻¹^Closed-sn : ∀ {Γ α σ τ ν} c t l r → Γ ⊢sn τ ∋ t → (σ ∷ Γ) ⊢sn α ∋ l → (τ ∷ Γ) ⊢sn α ∋ r →
  Γ ⊢sn ν ∋ cut (r [ t /0]) c → Γ ∣ α ⊢sn ν ∋ c →
  Closed (Γ ⊢ ν ∋_↝_) (Γ ⊢sn ν ∋_) (cut (`case (`i₂ t) l r) c)
ι₂⁻¹^Closed-sn c t l r t^sn@(sn t^sn′) l^sn@(sn l^sn′) r^sn@(sn r^sn′) c[r[t]]^sn@(sn c[r[t]]^sn′) c^sn red
  with cut⁻¹‿sn^↝ c^sn (cas (`i₂ t) l r) red
... | inj₁ (._ , refl , ι₂ .t .l .r)            = c[r[t]]^sn
... | inj₁ (._ , refl , [c]₁ ([i₂] red′) .l .r) =
  let c[r[t]]^sn′ = Closed⋆-sn c[r[t]]^sn (cut^↝⋆ c ([/0]^↝⋆ r red′)) in
  sn (ι₂⁻¹^Closed-sn c _ l r (t^sn′ red′) l^sn r^sn c[r[t]]^sn′ c^sn)
... | inj₁ (._ , refl , [c]₂ _ red′ .r)         =
  sn (ι₂⁻¹^Closed-sn c t _ r t^sn (l^sn′ red′) r^sn c[r[t]]^sn c^sn)
... | inj₁ (._ , refl , [c]₃ _ .l red′)         =
  sn (ι₂⁻¹^Closed-sn c t l _ t^sn l^sn (r^sn′ red′) (c[r[t]]^sn′ (cut^↝ c ([/0]^↝ red′ t))) c^sn)
... | inj₂ (c′ , refl , c′^sn , red′) =
  sn (ι₂⁻¹^Closed-sn c′ t l r t^sn l^sn r^sn (c[r[t]]^sn′ (red′ (r [ t /0]))) c′^sn)

ι₂⁻¹^sn : ∀ {Γ α σ τ ν} c t l r → Γ ⊢sn τ ∋ t → (σ ∷ Γ) ⊢sn α ∋ l → (τ ∷ Γ) ⊢sn α ∋ r →
  Γ ⊢sn ν ∋ cut (r [ t /0]) c → Γ ∣ α ⊢sn ν ∋ c → Γ ⊢sn ν ∋ cut (`case (`i₂ t) l r) c
ι₂⁻¹^sn c t l r t^sn l^sn r^sn c[r[t]]^sn c^sn =
  sn (ι₂⁻¹^Closed-sn c t l r t^sn l^sn r^sn c[r[t]]^sn c^sn)

-- Section 3.2 Inductive Definition of Strongly Normalizing Terms

infix 4 _⊢_∋_↝SN_<_ _⊢SN_∋_<_ _⊢SNe_∋_<_
data _⊢_∋_↝SN_<_ Γ τ : Term τ Γ → Term τ Γ → Size → Set
data _⊢SN_∋_<_ (Γ : List Type) : (σ : Type) → Term σ Γ → Size → Set
data _⊢SNe_∋_<_ (Γ : List Type) : (σ : Type) → Term σ Γ → Size → Set

data _⊢_∋_↝SN_<_ Γ τ where
-- computational
  β    : ∀ {σ i} t u → Γ ⊢SN σ ∋ u < i → Γ ⊢ τ ∋ `λ t `∙ u ↝SN t [ u /0] < ↑ i
  ι₁   : ∀ {σ₁ σ₂ i} t l r → Γ ⊢SN σ₁ ∋ t < i → (σ₂ ∷ Γ) ⊢SN τ ∋ r < i →
         Γ ⊢ τ ∋ `case (`i₁ t) l r ↝SN l [ t /0] < ↑ i
  ι₂   : ∀ {σ₁ σ₂ i} t l r → Γ ⊢SN σ₂ ∋ t < i → (σ₁ ∷ Γ) ⊢SN τ ∋ l < i →
         Γ ⊢ τ ∋ `case (`i₂ t) l r ↝SN r [ t /0] < ↑ i
-- structural
  [∙]₂ : ∀ {σ i f g} → Γ ⊢ σ ⇒ τ ∋ f ↝SN g < i → ∀ t → Γ ⊢ τ ∋ f `∙ t ↝SN g `∙ t < ↑ i
  [c]₁ : ∀ {σ₁ σ₂ i t u} → Γ ⊢ σ₁ + σ₂ ∋ t ↝SN u < i → ∀ l r →
         Γ ⊢ τ ∋ `case t l r ↝SN `case u l r < ↑ i

data _⊢SN_∋_<_ Γ where
  neu : ∀ {σ t i} → Γ ⊢SNe σ ∋ t < i → Γ ⊢SN σ ∋ t < ↑ i
  lam : ∀ {σ τ b i} → (σ ∷ Γ) ⊢SN τ ∋ b < i → Γ ⊢SN σ ⇒ τ ∋ `λ b < ↑ i
  inl : ∀ {σ τ t i} → Γ ⊢SN σ ∋ t < i → Γ ⊢SN σ + τ ∋ `i₁ t < ↑ i
  inr : ∀ {σ τ t i} → Γ ⊢SN τ ∋ t < i → Γ ⊢SN σ + τ ∋ `i₂ t < ↑ i
  red : ∀ {σ t t′ i} → Γ ⊢ σ ∋ t ↝SN t′ < i → Γ ⊢SN σ ∋ t′ < i → Γ ⊢SN σ ∋ t < ↑ i

data _⊢SNe_∋_<_ Γ where
  var : ∀ {σ i} v → Γ ⊢SNe σ ∋ `var v < ↑ i
  app : ∀ {σ τ f t i} → Γ ⊢SNe σ ⇒ τ ∋ f < i → Γ ⊢SN σ ∋ t < i → Γ ⊢SNe τ ∋ f `∙ t < ↑ i
  cas : ∀ {σ τ ν t l r i} → Γ ⊢SNe σ + τ ∋ t < i →
        (σ ∷ Γ) ⊢SN ν ∋ l < i → (τ ∷ Γ) ⊢SN ν ∋ r < i → Γ ⊢SNe ν ∋ `case t l r < ↑ i

infix 4 _⊢_∋_↝SN_ _⊢SN_∋_ _⊢SNe_∋_
_⊢_∋_↝SN_ = _⊢_∋_↝SN_< _
_⊢SN_∋_ = _⊢SN_∋_< _
_⊢SNe_∋_ = _⊢SNe_∋_< _

SN∋ : Pred Term
pred SN∋ = _ ⊢SN _ ∋_

SNe : Pred Term
pred SNe = _ ⊢SNe _ ∋_

[v↦v]^SNe : ∀ {Γ} → pred.∀[ SNe ] (base vl^Tm {Γ})
lookup^P [v↦v]^SNe v rewrite lookup-base^Tm {d = TermD} v = var v

infix 4 _∣_⊢SN_∋_<_ _∣_⊢SN_∋_
data _∣_⊢SN_∋_<_ Γ α : ∀ σ → Γ ∣ α ⊢ σ → Size → Set where
  <>  : ∀ {i} → Γ ∣ α ⊢SN α ∋ <> < ↑ i
  app : ∀ {i σ τ c t} → Γ ∣ α ⊢SN σ ⇒ τ ∋ c < i → Γ ⊢SN σ ∋ t < i → Γ ∣ α ⊢SN τ ∋ app c t < ↑ i
  cas : ∀ {i σ τ ν c l r} → Γ ∣ α ⊢SN σ + τ ∋ c < i →
        (σ ∷ Γ) ⊢SN ν ∋ l < i → (τ ∷ Γ) ⊢SN ν ∋ r < i → Γ ∣ α ⊢SN ν ∋ cas c l r < ↑ i

_∣_⊢SN_∋_ = _∣_⊢SN_∋_< _

∘C^SN : ∀ {Γ α β σ c c′} → Γ ∣ β ⊢SN σ ∋ c → Γ ∣ α ⊢SN β ∋ c′ → Γ ∣ α ⊢SN σ ∋ c ∘C c′
∘C^SN <>                   c′^SN = c′^SN
∘C^SN (app c^SN t^SN)      c′^SN = app (∘C^SN c^SN c′^SN) t^SN
∘C^SN (cas c^SN l^SN r^SN) c′^SN = cas (∘C^SN c^SN c′^SN) l^SN r^SN

cut⁻¹^SNe : ∀ {Γ τ t i} → Γ ⊢SNe τ ∋ t < i → ∃ λ ctx → let (σ , c) = ctx in
            ∃ λ v → t ≡ cut (`var v) c × Γ ∣ σ ⊢SN τ ∋ c < i
cut⁻¹^SNe (var v)          = _ , v , refl , <>
cut⁻¹^SNe (app f^SNe t^SN) =
  let (_ , v , eq , c^SN) = cut⁻¹^SNe f^SNe
  in _ , v , cong (_`∙ _) eq , app c^SN t^SN
cut⁻¹^SNe (cas t^SNe l^SN r^SN) =
  let (_ , v , eq , c^SN) = cut⁻¹^SNe t^SNe
  in _ , v , cong (λ t → `case t _ _) eq , cas c^SN l^SN r^SN

-- Lemma 4.11 Thinning
mutual

 -- 1.
 th^SN : ∀ {σ Γ Δ t} ρ → Γ ⊢SN σ ∋ t → Δ ⊢SN σ ∋ ren ρ t
 th^SN ρ (neu n)   = neu (th^SNe ρ n)
 th^SN ρ (lam t)   = lam (th^SN _ t)
 th^SN ρ (inl t)   = inl (th^SN ρ t)
 th^SN ρ (inr t)   = inr (th^SN ρ t)
 th^SN ρ (red r t) = red (th^↝SN ρ r) (th^SN ρ t)

 -- 2.
 th^SNe : ∀ {σ Γ Δ t} ρ → Γ ⊢SNe σ ∋ t → Δ ⊢SNe σ ∋ ren ρ t
 th^SNe ρ (var v)     = var (lookup ρ v)
 th^SNe ρ (app n t)   = app (th^SNe ρ n) (th^SN ρ t)
 th^SNe ρ (cas n l r) = cas (th^SNe ρ n) (th^SN _ l) (th^SN _ r)

 -- 3.
 th^↝SN : ∀ {σ Γ Δ t u} ρ → Γ ⊢ σ ∋ t ↝SN u → Δ ⊢ σ ∋ ren ρ t ↝SN ren ρ u
 th^↝SN ρ (β t u u^SN)         =
   subst (_ ⊢ _ ∋ ren ρ (`λ t `∙ u) ↝SN_< _) (sym $ renβ TermD t u ρ) (β _ (ren ρ u) (th^SN ρ u^SN))
 th^↝SN ρ (ι₁ t l r t^SN r^SN) =
   subst (_ ⊢ _ ∋ ren ρ (`case (`i₁ t) l r) ↝SN_< _) (sym $ renβ TermD l t ρ)
   $ ι₁ _ _ (ren _ r) (th^SN ρ t^SN) (th^SN _ r^SN)
 th^↝SN ρ (ι₂ t l r t^SN l^SN) =
   subst (_ ⊢ _ ∋ ren ρ (`case (`i₂ t) l r) ↝SN_< _) (sym $ renβ TermD r t ρ)
   $ ι₂ _ (ren _ l) _ (th^SN ρ t^SN) (th^SN _ l^SN)
 th^↝SN ρ ([∙]₂ r t)           = [∙]₂ (th^↝SN ρ r) (ren ρ t)
 th^↝SN ρ ([c]₁ r bl br)       = [c]₁ (th^↝SN ρ r) (ren _ bl) (ren _ br)

-- Lemma 4.12 Anti-Thinning
mutual

 -- 1.
 th⁻¹^SN : ∀ {σ Γ Δ t′} t ρ → t′ ≡ ren ρ t → Δ ⊢SN σ ∋ t′ → Γ ⊢SN σ ∋ t
 th⁻¹^SN t         ρ eq    (neu pr) = neu (th⁻¹^SNe t ρ eq pr)
 th⁻¹^SN (`λ t)    ρ refl  (lam pr) = lam (th⁻¹^SN t _ refl pr)
 th⁻¹^SN (`i₁ t)   ρ refl  (inl pr) = inl (th⁻¹^SN t ρ refl pr)
 th⁻¹^SN (`i₂ t)   ρ refl  (inr pr) = inr (th⁻¹^SN t ρ refl pr)
 th⁻¹^SN (`var v)  ρ ()    (lam pr)
 th⁻¹^SN (`var v)  ρ ()    (inl pr)
 th⁻¹^SN (`var v)  ρ ()    (inr pr)
 th⁻¹^SN t         ρ refl  (red r pr)  =
   let (t′ , eq , r′) = th⁻¹^↝SN t ρ r in red r′ (th⁻¹^SN t′ ρ eq pr)

 -- 2.
 th⁻¹^SNe : ∀ {σ Γ Δ t′} t ρ → t′ ≡ ren ρ t → Δ ⊢SNe σ ∋ t′ → Γ ⊢SNe σ ∋ t
 th⁻¹^SNe (`var v) ρ refl (var _)     = var v
 th⁻¹^SNe (f `∙ t) ρ refl (app rf rt) =
   app (th⁻¹^SNe f ρ refl rf) (th⁻¹^SN t ρ refl rt)
 th⁻¹^SNe (`case t l r) ρ refl (cas rt rl rr) =
   cas (th⁻¹^SNe t ρ refl rt) (th⁻¹^SN l _ refl rl) (th⁻¹^SN r _ refl rr)

 -- 3.
 th⁻¹^↝SN : ∀ {σ Γ Δ u} t ρ → Δ ⊢ σ ∋ ren ρ t ↝SN u → ∃ λ u′ → u ≡ ren ρ u′ × Γ ⊢ σ ∋ t ↝SN u′
 th⁻¹^↝SN (`var v)    ρ ()
 th⁻¹^↝SN (`λ b)      ρ ()
 th⁻¹^↝SN (`i₁ t)     ρ ()
 th⁻¹^↝SN (`i₂ t)     ρ ()
 -- reductions
 th⁻¹^↝SN (`λ b `∙ t)         ρ (β ._ ._ t^SN)             =
   b [ t /0] , sym (renβ TermD b t ρ) , β b t (th⁻¹^SN t ρ refl t^SN)
 th⁻¹^↝SN (`case (`i₁ t) l r) ρ (ι₁ ._ ._ ._ t^SN r^SN)    =
   l [ t /0] , sym (renβ TermD l t ρ) , ι₁ t l r (th⁻¹^SN t ρ refl t^SN) (th⁻¹^SN r _ refl r^SN)
 th⁻¹^↝SN (`case (`i₂ t) l r) ρ (ι₂ ._ ._ ._ t^SN l^SN)    =
   r [ t /0] , sym (renβ TermD r t ρ) , ι₂ t l r (th⁻¹^SN t ρ refl t^SN) (th⁻¹^SN l _ refl l^SN)
-- structural
 th⁻¹^↝SN (f `∙ t)        ρ ([∙]₂ r ._)    =
   let (g , eq , r′) = th⁻¹^↝SN f ρ r in g `∙ t , cong (_`∙ ren ρ t) eq , [∙]₂ r′ t
 th⁻¹^↝SN (`case c bl br) ρ ([c]₁ r ._ ._) = let (d , eq , r′) = th⁻¹^↝SN c ρ r in
   `case d bl br , cong (λ c → `case c (ren _ bl) (ren _ br)) eq , [c]₁ r′ bl br

-- Lemma 4.13 SNe is closed under application
_SNe∙_ : ∀ {Γ σ τ f t} → Γ ⊢SNe σ ⇒ τ ∋ f → Γ ⊢SN σ ∋ t → Γ ⊢SN τ ∋ f `∙ t
f^SNe SNe∙ t^SN = neu (app f^SNe t^SN)

-- Lemma 4.14: Extensionality of SN
SNe-ext : ∀ {Γ σ τ f} v → Γ ⊢SNe τ ∋ f `∙ `var v → Γ ⊢SNe σ ⇒ τ ∋ f
SNe-ext v (app f^SNe v^SN) = f^SNe

SN-ext : ∀ {Γ σ τ f} v → Γ ⊢SN τ ∋ f `∙ `var v → Γ ⊢SN σ ⇒ τ ∋ f
SN-ext v (neu fv^SNe)             = neu (SNe-ext v fv^SNe)
SN-ext v (red ([∙]₂ r _)   fv^SN) = red r (SN-ext v fv^SN)
SN-ext v (red (β t _ v^SN) fv^SN) = lam (th⁻¹^SN t (base vl^Var ∙ v) eq fv^SN) where
  eq = sym $ Sim.sim sim.RenSub (base^VarTm^R ∙^R refl) t

-- Section 4.3 Soundness (Short alternative proof)
infix 4 _⊢_∋_↝sn_<_ _⊢_∋_↝sn_
data _⊢_∋_↝sn_<_ Γ τ : (t u : Term τ Γ) → Size → Set where
  β    : ∀ {σ i} b u → Γ ⊢sn σ ∋ u → Γ ⊢ τ ∋ `λ b `∙ u ↝sn b [ u /0] < ↑ i
  ι₁   : ∀ {σ₁ σ₂ i} t l r → Γ ⊢sn σ₁ ∋ t < i → (σ₂ ∷ Γ) ⊢sn τ ∋ r < i →
         Γ ⊢ τ ∋ `case (`i₁ t) l r ↝sn l [ t /0] < ↑ i
  ι₂   : ∀ {σ₁ σ₂ i} t l r → Γ ⊢sn σ₂ ∋ t < i → (σ₁ ∷ Γ) ⊢sn τ ∋ l < i →
         Γ ⊢ τ ∋ `case (`i₂ t) l r ↝sn r [ t /0] < ↑ i
-- structural
  [∙]₂ : ∀ {σ i f g} → Γ ⊢ σ ⇒ τ ∋ f ↝sn g < i → ∀ t → Γ ⊢ τ ∋ f `∙ t ↝sn g `∙ t < ↑ i
  [c]₁ : ∀ {σ₁ σ₂ i t u} → Γ ⊢ σ₁ + σ₂ ∋ t ↝sn u < i → ∀ l r →
         Γ ⊢ τ ∋ `case t l r ↝sn `case u l r < ↑ i

_⊢_∋_↝sn_ = _⊢_∋_↝sn_< _

-- Lemma 4.17 Backwards closure of sn
↝sn⁻¹^sn : ∀ {Γ σ τ t′ t i} c → Γ ⊢ σ ∋ t′ ↝sn t < i →
           Γ ⊢sn τ ∋ cut t c → Γ ⊢sn τ ∋ cut t′ c
↝sn⁻¹^sn c (β b u u^sn) c[b[u]]^sn =
  let (c^sn , b[u]^sn) = cut⁻¹^sn (b [ u /0]) c c[b[u]]^sn in
  let b^sn = [/0]⁻¹^sn b u b[u]^sn in
  β⁻¹^sn b^sn u^sn c[b[u]]^sn c^sn
↝sn⁻¹^sn c (ι₁ t l r t^sn r^sn) c[l[t]]^sn =
  let (c^sn , l[t]^sn) = cut⁻¹^sn (l [ t /0]) c c[l[t]]^sn in
  let l^sn = [/0]⁻¹^sn l t l[t]^sn in
  ι₁⁻¹^sn c t l r t^sn l^sn r^sn c[l[t]]^sn c^sn
↝sn⁻¹^sn c (ι₂ t l r t^sn l^sn) c[r[t]]^sn =
  let (c^sn , r[t]^sn) = cut⁻¹^sn (r [ t /0]) c c[r[t]]^sn in
  let r^sn = [/0]⁻¹^sn r t r[t]^sn in
  ι₂⁻¹^sn c t l r t^sn l^sn r^sn c[r[t]]^sn c^sn
↝sn⁻¹^sn c ([∙]₂ r^sn u) c[ft]^sn =
  let eq t   = cut-∘C t c (app <> u) in
  let ft^sn′ = subst (_ ⊢sn _ ∋_) (eq _) c[ft]^sn in
  let ih     = ↝sn⁻¹^sn (c ∘C app <> u) r^sn ft^sn′ in
  subst (_ ⊢sn _ ∋_) (sym (eq _)) ih
↝sn⁻¹^sn c ([c]₁ r^sn l r) c[slr]^sn =
  let eq t    = cut-∘C t c (cas <> l r) in
  let slr^sn′ = subst (_ ⊢sn _ ∋_) (eq _) c[slr]^sn in
  let ih      = ↝sn⁻¹^sn (c ∘C cas <> l r) r^sn slr^sn′ in
  subst (_ ⊢sn _ ∋_) (sym (eq _)) ih

 -- Theorem 4.18 Soundness of SN
mutual
 -- 1.
 sound^SN : ∀ {Γ σ t i} → Γ ⊢SN σ ∋ t < i → Γ ⊢sn σ ∋ t
 sound^SN (neu t^SNe)  = let (_ , v , eq , c^SN) = cut⁻¹^SNe t^SNe in
                         subst (_ ⊢sn _ ∋_) (sym eq) (cut^sn _ (sound^∣SN c^SN))
 sound^SN (lam b^SN)   = `λ^sn (sound^SN b^SN)
 sound^SN (inl t^SN)   = `i₁^sn (sound^SN t^SN)
 sound^SN (inr t^SN)   = `i₂^sn (sound^SN t^SN)
 sound^SN (red r t^SN) = ↝sn⁻¹^sn <> (sound^↝SN r) (sound^SN t^SN)

 -- 2.
 sound^∣SN : ∀ {Γ α σ c i} → Γ ∣ α ⊢SN σ ∋ c < i → Γ ∣ α ⊢sn σ ∋ c
 sound^∣SN <>                   = <>
 sound^∣SN (app c^SN t^SN)      = app (sound^∣SN c^SN) (sound^SN t^SN)
 sound^∣SN (cas c^SN l^SN r^SN) = cas (sound^∣SN c^SN) (sound^SN l^SN) (sound^SN r^SN)

 -- 3.
 sound^↝SN : ∀ {Γ σ t u i} → Γ ⊢ σ ∋ t ↝SN u < i → Γ ⊢ σ ∋ t ↝sn u
 sound^↝SN (β t u u^SN)         = β t u (sound^SN u^SN)
 sound^↝SN (ι₁ t l r t^SN r^SN) = ι₁ t l r (sound^SN t^SN) (sound^SN r^SN)
 sound^↝SN (ι₂ t l r t^SN l^SN) = ι₂ t l r (sound^SN t^SN) (sound^SN l^SN)
 sound^↝SN ([∙]₂ r t)           = [∙]₂ (sound^↝SN r) t
 sound^↝SN ([c]₁ r _ _)         = [c]₁ (sound^↝SN r) _ _

-- Section 4.4 Soundness and Completeness

-- Theorem 4.16 Completeness of SN
-- We start with a definition of deeply nested β-redexes

data Elim (Γ : List Type) (τ : Type) : Type → Set where
  app : ∀ {σ} → Term σ Γ → Elim Γ τ (σ ⇒ τ)
  cas : ∀ {σ₁ σ₂} → Term τ (σ₁ ∷ Γ) → Term τ (σ₂ ∷ Γ) → Elim Γ τ (σ₁ + σ₂)

elim : ∀ {Γ σ τ} → Elim Γ τ σ → Γ ∣ σ ⊢ τ
elim (app t)   = app <> t
elim (cas l r) = cas <> l r

data Red (Γ : List Type) (τ : Type) : Set where
  β  : ∀ {σ}     → Term τ (σ ∷ Γ) → Term σ Γ → Red Γ τ
  ι₁ : ∀ {σ₁ σ₂} → Term σ₁ Γ → Term τ (σ₁ ∷ Γ) → Term τ (σ₂ ∷ Γ) → Red Γ τ
  ι₂ : ∀ {σ₁ σ₂} → Term σ₂ Γ → Term τ (σ₁ ∷ Γ) → Term τ (σ₂ ∷ Γ) → Red Γ τ

unRed : ∀ {Γ τ} → Red Γ τ → Term τ Γ
unRed (β b u)    = `λ b `∙ u
unRed (ι₁ t l r) = `case (`i₁ t) l r
unRed (ι₂ t l r) = `case (`i₂ t) l r

βιRed : ∀ {Γ τ} → Red Γ τ → Term τ Γ
βιRed (β b u)    = b [ u /0]
βιRed (ι₁ t l r) = l [ t /0]
βιRed (ι₂ t l r) = r [ t /0]

fire : ∀ {Γ τ} r → Γ ⊢ τ ∋ unRed r ↝ βιRed r
fire (β b u)     = β b u
fire (ι₁ t l r)  = ι₁ t l r
fire (ι₂ t l r)  = ι₂ t l r

mutual
  -- 1.
  complete^SNe : ∀ {Γ σ α i c} v → Γ ∣ α ⊢SN σ ∋ c →
    let t = cut (`var v) c in ∀ {t′} → t′ ≡ t → Γ ⊢sn σ ∋ t′ < i → Γ ⊢SNe σ ∋ t′
  complete^SNe v <>                refl c[v]^sn   = var v
  complete^SNe v (app c t^SN)      refl c[v]∙t^sn =
    app (complete^SNe v c refl (`∙t⁻¹^sn c[v]∙t^sn)) t^SN
  complete^SNe v (cas c l^SN r^SN) refl c[v]lr^sn =
    cas (complete^SNe v c refl (`case₁⁻¹^sn c[v]lr^sn)) l^SN r^SN

  -- 2.
  complete^SN-βι : ∀ {Γ α σ i} (r : Red Γ α) c →
    let t = cut (unRed r) c in Γ ⊢ σ ∋ t ↝SN cut (βιRed r) c →
    ∀ {t′} → t′ ≡ t → Γ ⊢sn σ ∋ t′ < i → Γ ⊢SN σ ∋ t′
  complete^SN-βι t c r refl (sn p) = red r (complete^SN _ (p (cut^↝ c (fire t))))

  -- 3.
  complete^SN : ∀ {Γ σ i} t → Γ ⊢sn σ ∋ t < i → Γ ⊢SN σ ∋ t
  complete^SN (`var v)      v^sn  = neu (var v)
  complete^SN (`i₁ t)       it^sn = inl (complete^SN t (`i₁⁻¹^sn it^sn))
  complete^SN (`i₂ t)       it^sn = inr (complete^SN t (`i₂⁻¹^sn it^sn))
  complete^SN (`λ b)        λb^sn = lam (complete^SN b (`λ⁻¹^sn λb^sn))
  complete^SN (f `∙ t)      ft^sn =
    let (f^sn , t^sn) = `∙⁻¹^sn ft^sn in
    let t^SN = complete^SN t t^sn in
    elim^SN f (app t) f^sn (app <> t^SN) ft^sn
  complete^SN (`case t l r) tlr^sn =
    let (t^sn , l^sn , r^sn) = `case⁻¹^sn tlr^sn in
    let (l^SN , r^SN) = (complete^SN l l^sn , complete^SN r r^sn) in
    elim^SN t (cas l r) t^sn (cas <> l^SN r^SN) tlr^sn

  elim^SN : ∀ {Γ σ τ i} t e → Γ ⊢sn σ ∋ t < i → Γ ∣ σ ⊢SN τ ∋ elim e →
               Γ ⊢sn τ ∋ cut t (elim e) < i → Γ ⊢SN τ ∋ cut t (elim e)
  elim^SN t e t^sn e^SN e[t]^sn =
    case spine^SN t e t^sn e^SN of λ where
      (_ , c , inj₁ (v , eq , c^SN)) → neu (complete^SNe v c^SN eq e[t]^sn)
      (_ , c , inj₂ (r , eq , r^SN)) → complete^SN-βι r c r^SN eq e[t]^sn

  spine^SN : ∀ {Γ σ τ i} t e → Γ ⊢sn σ ∋ t < i → Γ ∣ σ ⊢SN τ ∋ elim e →
             ∃ λ α → ∃ λ (c : Γ ∣ α ⊢ τ) →
      (∃ λ v → cut t (elim e) ≡ cut (`var v) c × Γ ∣ α ⊢SN τ ∋ c)
    ⊎ (∃ λ r → cut t (elim e) ≡ cut (unRed r) c
             × Γ ⊢ τ ∋ cut (unRed r) c ↝SN cut (βιRed r) c)
  spine^SN (`var v) e tm^sn e^SN = _ , elim e , inj₁ (v , refl , e^SN)
  spine^SN (`λ b) (app t) tm^sn (app <> t^SN) = _ , <> , inj₂ (β b t , refl , β b t t^SN)
  spine^SN (`i₁ t) (cas l r) tm^sn (cas <> l^SN r^SN) =
    let t^SN = complete^SN t (`i₁⁻¹^sn tm^sn) in
    _ , <> , inj₂ (ι₁ t l r , refl , ι₁ t l r t^SN r^SN)
  spine^SN (`i₂ t) (cas l r) tm^sn (cas <> l^SN r^SN) =
    let t^SN = complete^SN t (`i₂⁻¹^sn tm^sn) in
    _ , <> , inj₂ (ι₂ t l r , refl , ι₂ t l r t^SN l^SN)
  spine^SN (f `∙ t) e tm^sn e^SN =
    let (f^sn , t^sn) = `∙⁻¹^sn tm^sn in
    let t^SN = complete^SN t t^sn in
    case spine^SN f (app t) f^sn (app <> t^SN) of λ where
      (_ , c , inj₁ (v , eq , c^SN)) →
        _ , (elim e ∘C c) , inj₁ (v , spine-eq e c eq , ∘C^SN e^SN c^SN)
      (_ , c , inj₂ (r , eq , r^SN)) →
        _ , (elim e ∘C c) , inj₂ (r , spine-eq e c eq , spine-red e c r r^SN)
  spine^SN (`case t l r) e tm^sn e^SN =
    let (t^sn , l^sn , r^sn) = `case⁻¹^sn tm^sn in
    let (l^SN , r^SN) = (complete^SN l l^sn , complete^SN r r^sn) in
    case spine^SN t (cas l r) t^sn (cas <> l^SN r^SN) of λ where
      (_ , c , inj₁ (v , eq , c^SN)) →
        _ , (elim e ∘C c) , inj₁ (v , spine-eq e c eq , ∘C^SN e^SN c^SN)
      (_ , c , inj₂ (r , eq , r^SN)) →
        _ , (elim e ∘C c) , inj₂ (r , spine-eq e c eq , spine-red e c r r^SN)

  spine-eq : ∀ {Γ α β σ t tc} (e : Elim Γ σ β) (c : Γ ∣ α ⊢ β) →
             tc ≡ cut t c → cut tc (elim e) ≡ cut t (elim e ∘C c)
  spine-eq e c refl = cut-∘C _ (elim e) c

  spine-red : ∀ {Γ α β σ} e c → (r : Red Γ α) →
              Γ ⊢ β ∋ cut (unRed r) c ↝SN cut (βιRed r) c →
              Γ ⊢ σ ∋ cut (unRed r) (elim e ∘C c) ↝SN cut (βιRed r) (elim e ∘C c)
  spine-red (app t)   c r r^SN = [∙]₂ r^SN t
  spine-red (cas _ _) c r r^SN = [c]₁ r^SN _ _

-- Section 5 Reducibility Candidates
-------------------------------------------------------------------
infix 3 _+𝓡_
data _+𝓡_ {Γ σ τ} (𝓢 : Term σ Γ → Set) (𝓣 : Term τ Γ → Set) : Term (σ + τ) Γ → Set where
  -- values
  inl : ∀ {t} → 𝓢 t → (𝓢 +𝓡 𝓣) (`i₁ t)
  inr : ∀ {t} → 𝓣 t → (𝓢 +𝓡 𝓣) (`i₂ t)
  neu : ∀ {t} → Γ ⊢SNe σ + τ ∋ t → (𝓢 +𝓡 𝓣) t
  -- closed under anti-reduction
  red : ∀ {t u} → Γ ⊢ σ + τ ∋ t ↝SN u → (𝓢 +𝓡 𝓣) u → (𝓢 +𝓡 𝓣) t

infix 3 _⊢𝓡_∋_
_⊢𝓡_∋_     : ∀ Γ σ → Term σ Γ → Set
Γ ⊢𝓡 α     ∋ t = Γ ⊢SN α ∋ t
Γ ⊢𝓡 σ + τ ∋ t = ((Γ ⊢𝓡 σ ∋_) +𝓡 (Γ ⊢𝓡 τ ∋_)) t
Γ ⊢𝓡 σ ⇒ τ ∋ t = ∀ {Δ} ρ {u} → Δ ⊢𝓡 σ ∋ u → Δ ⊢𝓡 τ ∋ ren ρ t `∙ u

𝓡^P : Pred Term
pred 𝓡^P = _ ⊢𝓡 _ ∋_

-- Theorem 5.1
mutual

 -- 1.
 quote^𝓡 : ∀ {Γ} σ {t} → Γ ⊢𝓡 σ ∋ t → Γ ⊢SN σ ∋ t
 quote^𝓡 α       t^𝓡         = t^𝓡
 quote^𝓡 (σ + τ) (inl t^𝓡)   = inl (quote^𝓡 σ t^𝓡)
 quote^𝓡 (σ + τ) (inr t^𝓡)   = inr (quote^𝓡 τ t^𝓡)
 quote^𝓡 (σ + τ) (neu t^SNe)  = neu t^SNe
 quote^𝓡 (σ + τ) (red r t^𝓡) = red r (quote^𝓡 (σ + τ) t^𝓡)
 quote^𝓡 (σ ⇒ τ) t^𝓡         = th⁻¹^SN _ embed refl (SN-ext z tz^SN)
   where z^𝓡  = unquote^𝓡 σ (var z)
         embed = pack s
         tz^SN = quote^𝓡 τ (t^𝓡 embed z^𝓡)

 -- 2.
 unquote^𝓡 : ∀ {Γ} σ {t} → Γ ⊢SNe σ ∋ t → Γ ⊢𝓡 σ ∋ t
 unquote^𝓡 α       t^SNe        = neu t^SNe
 unquote^𝓡 (σ + τ) t^SNe        = neu t^SNe
 unquote^𝓡 (σ ⇒ τ) t^SNe ρ u^𝓡 = unquote^𝓡 τ (app (th^SNe ρ t^SNe) u^SN)
   where u^SN = quote^𝓡 σ u^𝓡

-- 3.
↝SN⁻¹^𝓡 : ∀ {Γ} σ {t′ t} → Γ ⊢ σ ∋ t′ ↝SN t → Γ ⊢𝓡 σ ∋ t → Γ ⊢𝓡 σ ∋ t′
↝SN⁻¹^𝓡 α       r t^𝓡 = red r t^𝓡
↝SN⁻¹^𝓡 (σ + τ) r t^𝓡 = red r t^𝓡
↝SN⁻¹^𝓡 (σ ⇒ τ) r t^𝓡 = λ ρ u^𝓡 → ↝SN⁻¹^𝓡 τ ([∙]₂ (th^↝SN ρ r) _) (t^𝓡 ρ u^𝓡)

th^𝓡 : ∀ {Γ Δ} σ ρ t → Γ ⊢𝓡 σ ∋ t → Δ ⊢𝓡 σ ∋ ren ρ t
th^𝓡 α       ρ t t^𝓡         = th^SN ρ t^𝓡
th^𝓡 (σ + τ) ρ _ (inl t^𝓡)   = inl (th^𝓡 σ ρ _ t^𝓡)
th^𝓡 (σ + τ) ρ _ (inr t^𝓡)   = inr (th^𝓡 τ ρ _ t^𝓡)
th^𝓡 (σ + τ) ρ t (neu t^SNe)  = neu (th^SNe ρ t^SNe)
th^𝓡 (σ + τ) ρ t (red r t^𝓡) = red (th^↝SN ρ r) (th^𝓡 (σ + τ) ρ _ t^𝓡)
th^𝓡 (σ ⇒ τ) ρ t t^𝓡 ρ′ u^𝓡 = cast (t^𝓡 (select ρ ρ′) u^𝓡)
  where cast = subst (λ t → _ ⊢𝓡 _ ∋ t `∙ _) (sym $ ren² TermD t ρ ρ′)

_∙^𝓡_ : ∀ {σ τ Γ f t} → Γ ⊢𝓡 σ ⇒ τ ∋ f → Γ ⊢𝓡 σ ∋ t → Γ ⊢𝓡 τ ∋ f `∙ t
_∙^𝓡_ {σ} {τ} {Γ} {f} {t} f^𝓡 t^𝓡 = cast (f^𝓡 (base vl^Var) t^𝓡)
  where cast = subst (λ f → Γ ⊢𝓡 τ ∋ f `∙ t) (ren-id f)

reify^𝓡 : ∀ σ τ {Γ Δ i} (l : Tm TermD i τ (σ ∷ Γ)) (ρ : (Γ ─Env) Term Δ) →
  Kripke^P 𝓡^P 𝓡^P (σ ∷ []) τ (Sem.body Substitution ρ (σ ∷ []) τ l) →
  (σ ∷ Δ) ⊢SN τ ∋ sub (lift vl^Tm (σ ∷ []) ρ) l
reify^𝓡 σ τ l ρ l^P = cast (quote^𝓡 τ val) where

  val  = l^P extend (ε^P ∙^P unquote^𝓡 σ (var z))

  sub^R : rel.∀[ Eq^R ] _ (lift vl^Tm (σ ∷ []) ρ)
  lookup^R sub^R z      = refl
  lookup^R sub^R (s v)  = Sim.sim RenExt extend-is-fresh (lookup ρ v)

  cast = subst (_ ⊢SN _ ∋_) (Sim.sim SubExt sub^R l)

[/0]^𝓡 :
  ∀ σ τ {Γ Δ i} t (l : Tm TermD i τ (σ ∷ Γ)) (ρ : (Γ ─Env) Term Δ) →
  Δ ⊢𝓡 σ ∋ t →
  Kripke^P 𝓡^P 𝓡^P (σ ∷ []) τ (Sem.body Substitution ρ (σ ∷ []) τ l) →
  Δ ⊢𝓡 τ ∋ sub (lift vl^Tm (σ ∷ []) ρ) l [ t /0]
[/0]^𝓡 σ τ t l ρ t^P l^P = cast (l^P (base vl^Var) (ε^P ∙^P t^P)) where

  ren^R : rel.∀[ VarTm^R ] (base vl^Var) (select (freshʳ vl^Var (σ ∷ [])) (base vl^Tm ∙ t))
  lookup^R ren^R v = sym (lookup-base^Tm (lookup (base vl^Var) v))

  sub^R : rel.∀[ Eq^R ] (sub (t /0]) <$> lift vl^Tm (σ ∷ []) ρ)
                        ((ε ∙ t) >> th^Env (th^𝓥 vl^Tm) ρ (base vl^Var))
  lookup^R sub^R z      = refl
  lookup^R sub^R (s v)  = begin
    sub (base vl^Tm ∙ t) (ren (freshʳ vl^Var (σ ∷ [])) (lookup ρ v))
      ≡⟨ rensub TermD (lookup ρ v) _ _ ⟩
    sub (select (freshʳ vl^Var (σ ∷ [])) (base vl^Tm ∙ t)) (lookup ρ v)
      ≡⟨ sym $ Sim.sim sim.RenSub ren^R (lookup ρ v) ⟩
    ren (base vl^Var) (lookup ρ v) ∎

  cast = subst (_ ⊢𝓡 _ ∋_) (sym (Fus.fus (Sub² TermD) sub^R l))

case^𝓡 : ∀ {i σ τ ν Γ Δ} (t : Term (σ + τ) Δ)
  (l : Tm TermD i ν (σ ∷ Γ)) (r : Tm TermD i ν (τ ∷ Γ))
  (ρ : (Γ ─Env) Term Δ) → Δ ⊢𝓡 σ + τ ∋ t →
  Kripke^P 𝓡^P 𝓡^P (σ ∷ []) ν (Sem.body Substitution ρ (σ ∷ []) ν l) →
  Kripke^P 𝓡^P 𝓡^P (τ ∷ []) ν (Sem.body Substitution ρ (τ ∷ []) ν r) →
  Δ ⊢𝓡 ν ∋ `case t (sub (lift vl^Tm (σ ∷ []) ρ) l) (sub (lift vl^Tm (τ ∷ []) ρ) r)
case^𝓡 (`i₁ t) bl br ρ (inl t^P)   bl^P br^P =
  ↝SN⁻¹^𝓡 _ (ι₁ t (sub _ bl) (sub _ br) (quote^𝓡 _ t^P) (reify^𝓡 _ _ br ρ br^P))
             ([/0]^𝓡 _ _ t bl ρ t^P bl^P)
case^𝓡 (`i₂ t) bl br ρ (inr t^P)   bl^P br^P =
  ↝SN⁻¹^𝓡 _ (ι₂ t (sub _ bl) (sub _ br) (quote^𝓡 _ t^P) (reify^𝓡 _ _ bl ρ bl^P))
             ([/0]^𝓡 _ _ t br ρ t^P br^P)
case^𝓡 t        bl br ρ (neu t^SNe) bl^P br^P =
  unquote^𝓡 _ (cas t^SNe (reify^𝓡 _ _ bl ρ bl^P) (reify^𝓡 _ _ br ρ br^P))
case^𝓡 t        bl br ρ (red r t^P) bl^P br^P =
  ↝SN⁻¹^𝓡 _ ([c]₁ r (sub _ bl) (sub _ br)) (case^𝓡 _ bl br ρ t^P bl^P br^P)

-- Section 6 Proving strong normalization
-------------------------------------------------------------------

-- Lemma 6.1 Fundamental lemma
fundamental : Fdm 𝓡^P 𝓡^P TermD Substitution
Fdm.th^P  fundamental {σ} {v = v} = λ ρ v^𝓡 → th^𝓡 σ ρ v v^𝓡
Fdm.var^P fundamental = λ x → x
Fdm.alg^P fundamental = alg^P where

  alg^P : ∀ {Γ Δ σ s} (b : ⟦ TermD ⟧ (Scope (Tm TermD s)) σ Γ) {ρ : (Γ ─Env) Term Δ} →
          let v = fmap TermD (Sem.body Substitution ρ) b in
          pred.∀[ 𝓡^P ] ρ → All TermD (Kripke^P 𝓡^P 𝓡^P) v → Δ ⊢𝓡 σ ∋ Sem.alg Substitution v
  -- case anlaysis
  alg^P (`case' t l r) {ρ} ρ^P (t^P , l^P , r^P , _) = case^𝓡 (sub ρ t) l r ρ t^P l^P r^P
  -- constructors
  alg^P (`i₁' t)           ρ^P (t^P , _)  = inl t^P
  alg^P (`i₂' t)           ρ^P (t^P , _)  = inr t^P
  -- application
  alg^P (f `∙' t)          ρ^P (f^P , t^P , _)       = f^P ∙^𝓡 t^P
  -- lambda abstraction
  alg^P (`λ' b) {ρ₁}       ρ^P (b^P , _) ρ {u} u^𝓡 =
    ↝SN⁻¹^𝓡 _ β-step $ cast (b^P ρ (ε^P ∙^P u^𝓡))
  -- at this point the substitution looks HORRIBLE
    where
      β-step = β (ren _ (sub _ b)) _ (quote^𝓡 _ u^𝓡)
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

      cast = subst (_ ⊢𝓡 _ ∋_) eq

eval : ∀ {Γ Δ σ ρ} → pred.∀[ 𝓡^P ] ρ → (t : Term σ Γ) → Δ ⊢𝓡 σ ∋ sub ρ t
eval = Fdm.fdm fundamental

-- Corollary 6.2
dummy : ∀ {Γ} → pred.∀[ 𝓡^P ] (base vl^Tm {Γ})
lookup^P dummy v rewrite lookup-base^Tm {d = TermD} v = unquote^𝓡 _ (var v)

_^SN : ∀ {Γ σ} t → Γ ⊢SN σ ∋ t
t ^SN = cast (quote^𝓡 _ (eval dummy t))
  where cast  = subst (_ ⊢SN _ ∋_) (sub-id t)

_^sn : ∀ {Γ σ} t → Γ ⊢sn σ ∋ t
t ^sn = sound^SN (t ^SN)
\end{code}

module Motivation.POPLMark2.GodelT where

open import indexed
open import var hiding (_<$>_)
open import varlike
open import environment
open import pred
open import rel
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
  ℕ   : Type
  _+_ : Type → Type → Type
  _⇒_ : Type → Type → Type

data TermC : Set where
  Lam App  : Type → Type → TermC
  InL InR  : Type → Type → TermC
  Cas      : Type → Type → Type → TermC
  Zro Suc  : TermC
  Rec      : Type → TermC

TermD : Desc Type
TermD =  `σ TermC λ where
  (Lam σ τ)    → `X (σ ∷ []) τ (`∎ (σ ⇒ τ))
  (App σ τ)    → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ))
  (InL σ τ)    → `X [] σ (`∎ (σ + τ))
  (InR σ τ)    → `X [] τ (`∎ (σ + τ))
  (Cas σ τ ν)  → `X [] (σ + τ) (`X (σ ∷ []) ν (`X (τ ∷ []) ν (`∎ ν)))
  Zro          → `∎ ℕ
  Suc          → `X [] ℕ (`∎ ℕ)
  (Rec σ)      → `X [] σ (`X (σ ∷ ℕ ∷ []) σ (`X [] ℕ (`∎ σ)))

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
pattern `0'           = (Zro , refl)
pattern `1+' t        = (Suc , t , refl)
pattern `rec' ze su t = (Rec _ , ze , su , t , refl)

pattern `λ  b         = `con (`λ' b)
pattern _`∙_ f t      = `con (f `∙' t)
pattern `i₁ t         = `con (`i₁' t)
pattern `i₂ t         = `con (`i₂' t)
pattern `case t l r   = `con (`case' t l r)
pattern `0            = `con `0'
pattern `1+ t         = `con (`1+' t)
pattern `rec ze su t  = `con (`rec' ze su t)

{-# DISPLAY `con (Lam _ _ , b , refl)           = `λ b         #-}
{-# DISPLAY `con (App _ _ , f , t , refl)       = f `∙ t       #-}
{-# DISPLAY `con (InL _ _ , t , refl)           = `i₁ t        #-}
{-# DISPLAY `con (InR _ _ , t , refl)           = `i₂ t        #-}
{-# DISPLAY `con (Cas _ _ _ , t , l , r , refl) = `case t l r  #-}
{-# DISPLAY `con (Zro , refl)                   = `0           #-}
{-# DISPLAY `con (Suc , t , refl)               = `1+ t        #-}
{-# DISPLAY `con (Rec , ze , su , t , refl)     = `rec ze su t #-}

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
  ιz   : ∀ {σ} ze su → Γ ⊢ σ ∋ `rec ze su `0 ↝ ze
  ιs   : ∀ {σ} ze su t → Γ ⊢ σ ∋ `rec ze su (`1+ t) ↝ sub (base vl^Tm ∙ t ∙ `rec ze su t) su
-- structural
  [λ]  : ∀ {σ τ t u} → (σ ∷ Γ) ⊢ τ ∋ t ↝ u → Γ ⊢ σ ⇒ τ ∋ `λ t ↝ `λ u
  [∙]₁ : ∀ {σ τ t u} f → Γ ⊢ σ ∋ t ↝ u → Γ ⊢ τ ∋ f `∙ t ↝ f `∙ u
  [∙]₂ : ∀ {σ τ f g} → Γ ⊢ σ ⇒ τ ∋ f ↝ g → ∀ t → Γ ⊢ τ ∋ f `∙ t ↝ g `∙ t
  [i₁] : ∀ {σ τ t u} → Γ ⊢ σ ∋ t ↝ u → Γ ⊢ σ + τ ∋ `i₁ t ↝ `i₁ u
  [i₂] : ∀ {σ τ t u} → Γ ⊢ τ ∋ t ↝ u → Γ ⊢ σ + τ ∋ `i₂ t ↝ `i₂ u
  [1+] : ∀ {t u} → Γ ⊢ ℕ ∋ t ↝ u → Γ ⊢ ℕ ∋ `1+ t ↝ `1+ u
  [c]₁ : ∀ {σ τ ν t u} → Γ ⊢ σ + τ ∋ t ↝ u → ∀ l r → Γ ⊢ ν ∋ `case t l r ↝ `case u l r
  [c]₂ : ∀ {σ τ ν l m} → ∀ t → σ ∷ Γ ⊢ ν ∋ l ↝ m → (r : Term ν (τ ∷ Γ)) → Γ ⊢ ν ∋ `case t l r ↝ `case t m r
  [c]₃ : ∀ {σ τ ν r s} → ∀ t → (l : Term ν (σ ∷ Γ)) → τ ∷ Γ ⊢ ν ∋ r ↝ s → Γ ⊢ ν ∋ `case t l r ↝ `case t l s
  [r]₁ : ∀ {σ ze ze′} → Γ ⊢ σ ∋ ze ↝ ze′ → ∀ su t → Γ ⊢ σ ∋ `rec ze su t ↝ `rec ze′ su t
  [r]₂ : ∀ {σ su su′} ze → σ ∷ ℕ ∷ Γ ⊢ σ ∋ su ↝ su′ → ∀ t → Γ ⊢ σ ∋ `rec ze su t ↝ `rec ze su′ t
  [r]₃ : ∀ {σ t t′} ze su → Γ ⊢ ℕ ∋ t ↝ t′ → Γ ⊢ σ ∋ `rec ze su t ↝ `rec ze su t′

tgt : ∀ {Γ σ t u} → Γ ⊢ σ ∋ t ↝ u → Term σ Γ
tgt {u = u} _ = u

_⊢_∋_↝⋆_ : ∀ Γ σ → Term σ Γ → Term σ Γ → Set
Γ ⊢ σ ∋ t ↝⋆ u = Star (Γ ⊢ σ ∋_↝_) t u

-- Lemma 1.2
-- Stability of Reduction under thinning and substitution
-- (Stability of Typing is a consequence of Term being a typed syntax)

th^↝ : ∀ {σ Γ Δ t u} ρ → Γ ⊢ σ ∋ t ↝ u → Δ ⊢ σ ∋ ren ρ t ↝ ren ρ u
th^↝ ρ (β t u)        = subst (_ ⊢ _ ∋ ren ρ (`λ t `∙ u) ↝_) (renβ TermD t (ε ∙ u) ρ) (β _ _)
th^↝ ρ (ι₁ t l r)     = subst (_ ⊢ _ ∋ ren ρ (`case (`i₁ t) l r) ↝_) (renβ TermD l (ε ∙ t) ρ) (ι₁ _ _ _)
th^↝ ρ (ι₂ t l r)     = subst (_ ⊢ _ ∋ ren ρ (`case (`i₂ t) l r) ↝_) (renβ TermD r (ε ∙ t) ρ) (ι₂ _ _ _)
th^↝ ρ (ιz ze su)     = ιz (ren ρ ze) (ren _ su)
th^↝ ρ (ιs ze su t)   = subst (_ ⊢ _ ∋ ren ρ (`rec ze su (`1+ t)) ↝_) (renβ TermD su (ε ∙ t ∙ `rec ze su t) ρ) (ιs _ _ _)
th^↝ ρ ([λ] r)        = [λ] (th^↝ _ r)
th^↝ ρ ([∙]₁ f r)     = [∙]₁ (ren ρ f) (th^↝ ρ r)
th^↝ ρ ([∙]₂ r t)     = [∙]₂ (th^↝ ρ r) (ren ρ t)
th^↝ ρ ([i₁] c)       = [i₁] (th^↝ ρ c)
th^↝ ρ ([i₂] c)       = [i₂] (th^↝ ρ c)
th^↝ ρ ([1+] c)       = [1+] (th^↝ ρ c)
th^↝ ρ ([c]₁ c l r)   = [c]₁ (th^↝ ρ c) (ren _ l) (ren _ r)
th^↝ ρ ([c]₂ t c r)   = [c]₂ (ren ρ t) (th^↝ _ c) (ren _ r)
th^↝ ρ ([c]₃ t l c)   = [c]₃ (ren ρ t) (ren _ l) (th^↝ _ c)
th^↝ ρ ([r]₁ c su t)  = [r]₁ (th^↝ ρ c) (ren _ su) (ren ρ t)
th^↝ ρ ([r]₂ ze c t)  = [r]₂ (ren ρ ze) (th^↝ _ c) (ren ρ t)
th^↝ ρ ([r]₃ ze su c) = [r]₃ (ren ρ ze) (ren _ su) (th^↝ ρ c)

-- Lemma 1.3
sub^↝ : ∀ {σ Γ Δ t u} ρ → Γ ⊢ σ ∋ t ↝ u → Δ ⊢ σ ∋ sub ρ t ↝ sub ρ u
sub^↝ ρ (β t u)        = subst (_ ⊢ _ ∋ sub ρ (`λ t `∙ u) ↝_) (subβ TermD t (ε ∙ u) ρ) (β _ _)
sub^↝ ρ (ι₁ t l r)     = subst (_ ⊢ _ ∋ sub ρ (`case (`i₁ t) l r) ↝_) (subβ TermD l (ε ∙ t) ρ) (ι₁ _ _ _)
sub^↝ ρ (ι₂ t l r)     = subst (_ ⊢ _ ∋ sub ρ (`case (`i₂ t) l r) ↝_) (subβ TermD r (ε ∙ t) ρ) (ι₂ _ _ _)
sub^↝ ρ (ιz ze su)     = ιz (sub ρ ze) (sub _ su)
sub^↝ ρ (ιs ze su t)   = subst (_ ⊢ _ ∋ sub ρ (`rec ze su (`1+ t)) ↝_) (subβ TermD su (ε ∙ t ∙ `rec ze su t) ρ) (ιs _ _ _)
sub^↝ ρ ([λ] r)        = [λ] (sub^↝ _ r)
sub^↝ ρ ([∙]₁ f r)     = [∙]₁ (sub ρ f) (sub^↝ ρ r)
sub^↝ ρ ([∙]₂ r t)     = [∙]₂ (sub^↝ ρ r) (sub ρ t)
sub^↝ ρ ([i₁] c)       = [i₁] (sub^↝ ρ c)
sub^↝ ρ ([i₂] c)       = [i₂] (sub^↝ ρ c)
sub^↝ ρ ([1+] c)       = [1+] (sub^↝ ρ c)
sub^↝ ρ ([c]₁ c l r)   = [c]₁ (sub^↝ ρ c) (sub _ l) (sub _ r)
sub^↝ ρ ([c]₂ t c r)   = [c]₂ (sub ρ t) (sub^↝ _ c) (sub _ r)
sub^↝ ρ ([c]₃ t l c)   = [c]₃ (sub ρ t) (sub _ l) (sub^↝ _ c)
sub^↝ ρ ([r]₁ r su t)  = [r]₁ (sub^↝ ρ r) (sub _ su) (sub ρ t)
sub^↝ ρ ([r]₂ ze r t)  = [r]₂ (sub ρ ze) (sub^↝ _ r) (sub ρ t)
sub^↝ ρ ([r]₃ ze su r) = [r]₃ (sub ρ ze) (sub _ su) (sub^↝ ρ r)

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
    `0' ρ^R (refl , _) → S.ε
    (`1+' t) ρ^R (refl , t^R , _) → S.gmap `1+ [1+] t^R
    (`case' t l r) {ρ₁} {ρ₂} ρ^R (refl , t^R , l^R , r^R , _) →
      S.gmap _ (λ c → [c]₁ c (sub _ l) (sub _ r)) t^R
      S.◅◅ S.gmap _ (λ c → [c]₂ (sub ρ₂ t) c (sub _ r)) (l^R _ [v↦t↝⋆t])
      S.◅◅ S.gmap  _ ([c]₃ (sub ρ₂ t) (sub _ l)) (r^R _  [v↦t↝⋆t])
    (`rec' ze su t) ρ^R (refl , ze^R , su^R , t^R , _) →
      S.gmap _ (λ c → [r]₁ c (sub _ su) (sub _ t)) ze^R
      S.◅◅ S.gmap _ (λ c → [r]₂ (sub _ ze) c (sub _ t)) (su^R _ [v↦t↝⋆t])
      S.◅◅ S.gmap _ ([r]₃ (sub _ ze) (sub _ su)) t^R

[/0]^↝⋆ : ∀ {σ τ Γ} t {u u′} → Γ ⊢ σ ∋ u ↝ u′ → Γ ⊢ τ ∋ t [ u /0] ↝⋆ t [ u′ /0]
[/0]^↝⋆ t r = sub^↝⋆ t ([v↦t↝⋆t] ∙^R S.return r)

-- Inversion lemmas for the interaction between ren, ∙, λ and ↝

th⁻¹^`∙ : ∀ {σ τ Γ Δ} (u : Term τ Γ) {f : Term (σ ⇒ τ) Δ} {t} ρ → f `∙ t ≡ ren ρ u →
          ∃ λ f′ → ∃ λ t′ → f′ `∙ t′ ≡ u × f ≡ ren ρ f′ × t ≡ ren ρ t′
th⁻¹^`∙ (f′ `∙ t′)     ρ refl = f′ , t′ , refl , refl , refl
th⁻¹^`∙ (`var _)       ρ ()

th⁻¹^`λ : ∀ {σ τ Γ Δ} (u : Term (σ ⇒ τ) Γ) {b : Term τ (σ ∷ Δ)} ρ → `λ b ≡ ren ρ u →
          ∃ λ b′ → `λ b′ ≡ u × b ≡ ren (lift vl^Var (σ ∷ []) ρ) b′
th⁻¹^`λ (`λ b′)        ρ refl = b′ , refl , refl
th⁻¹^`λ (`var v)       ρ ()


th⁻¹^↝ : ∀ {σ Γ Δ u′} t ρ → Δ ⊢ σ ∋ ren ρ t ↝ u′ →
          ∃ λ u → u′ ≡ ren ρ u × Γ ⊢ σ ∋ t ↝ u
th⁻¹^↝ (`var v) ρ ()
th⁻¹^↝ `0 ρ ()
-- redex
th⁻¹^↝ (`λ b `∙ t)           ρ (β _ _)    = b [ t /0] , renβ TermD b (ε ∙ t) ρ , β b t
th⁻¹^↝ (`case (`i₁ t) b₁ b₂) ρ (ι₁ _ _ _) = b₁ [ t /0] , renβ TermD b₁ (ε ∙ t) ρ , ι₁ t b₁ b₂
th⁻¹^↝ (`case (`i₂ t) b₁ b₂) ρ (ι₂ _ _ _) = b₂ [ t /0] , renβ TermD b₂ (ε ∙ t) ρ , ι₂ t b₁ b₂
th⁻¹^↝ (`rec ze su `0)       ρ (ιz _ _)   = ze , refl , ιz ze su
th⁻¹^↝ (`rec ze su (`1+ t))  ρ (ιs _ _ _) =
  sub (base vl^Tm ∙ t ∙ `rec ze su t) su , renβ TermD su (ε ∙ t ∙ `rec ze su t) ρ , ιs ze su t
-- structural
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
th⁻¹^↝ (`1+ t) ρ ([1+] r) =
  let (t′ , eq , r′) = th⁻¹^↝ t ρ r in (`1+ t′ , cong `1+ eq , [1+] r′)
th⁻¹^↝ (`case t b₁ b₂) ρ ([c]₁ r _ _) = let (t′ , eq , r′) = th⁻¹^↝ t ρ r in
  (`case t′ b₁ b₂ , cong (λ r → `case r (ren _ b₁) (ren _ b₂)) eq , [c]₁ r′ b₁ b₂)
th⁻¹^↝ (`case t b₁ b₂) ρ ([c]₂ _ r _) = let (b₁′ , eq , r′) = th⁻¹^↝ b₁ _ r in
  (`case t b₁′ b₂ , cong (λ r → `case (ren ρ t) r (ren _ b₂)) eq , [c]₂ t r′ b₂)
th⁻¹^↝ (`case t b₁ b₂) ρ ([c]₃ _ _ r) = let (b₂′ , eq , r′) = th⁻¹^↝ b₂ _ r in
  (`case t b₁ b₂′ , cong (`case (ren ρ t) (ren _ b₁)) eq , [c]₃ t b₁ r′)
th⁻¹^↝ (`rec ze su t) ρ ([r]₁ r _ _) = let (ze′ , eq , r′) = th⁻¹^↝ ze _ r in
  (`rec ze′ su t , cong (λ r → `rec r (ren _ su) (ren ρ t)) eq , [r]₁ r′ su t)
th⁻¹^↝ (`rec ze su t) ρ ([r]₂ _ r _) = let (su′ , eq , r′) = th⁻¹^↝ su _ r in
  (`rec ze su′ t , cong (λ r → `rec (ren ρ ze) r (ren ρ t)) eq , [r]₂ ze r′ t)
th⁻¹^↝ (`rec ze su t) ρ ([r]₃ _ _ r) = let (t′ , eq , r′) = th⁻¹^↝ t _ r in
  (`rec ze su t′ , cong (`rec (ren ρ ze) (ren _ su)) eq , [r]₃ ze su r′)

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

`0^sn : ∀ {Γ} → Γ ⊢sn ℕ ∋ `0
`0^sn = sn λ ()

`1+^sn : ∀ {Γ t} → Γ ⊢sn ℕ ∋ t → Γ ⊢sn ℕ ∋ `1+ t
`1+^sn (sn t^R) = sn λ { ([1+] r) → `1+^sn (t^R r) }

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

`1+⁻¹^sn : ∀ {Γ t i} → Γ ⊢sn ℕ ∋ `1+ t < i → Γ ⊢sn ℕ ∋ t < i
`1+⁻¹^sn (sn st^sn) = sn (λ r → `1+⁻¹^sn (st^sn ([1+] r)))

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

-- 7.
`rec₁⁻¹^sn : ∀ {σ Γ ze su t i} → Γ ⊢sn σ ∋ `rec ze su t < i → Γ ⊢sn σ ∋ ze < i
`rec₁⁻¹^sn (sn r^sn) = sn (λ r → `rec₁⁻¹^sn (r^sn ([r]₁ r _ _)))

`rec₂⁻¹^sn : ∀ {σ Γ ze su t i} → Γ ⊢sn σ ∋ `rec ze su t < i → (σ ∷ ℕ ∷ Γ) ⊢sn σ ∋ su < i
`rec₂⁻¹^sn (sn r^sn) = sn (λ r → `rec₂⁻¹^sn (r^sn ([r]₂ _ r _)))

`rec₃⁻¹^sn : ∀ {σ Γ ze su t i} → Γ ⊢sn σ ∋ `rec ze su t < i → Γ ⊢sn ℕ ∋ t < i
`rec₃⁻¹^sn (sn r^sn) = sn (λ r → `rec₃⁻¹^sn (r^sn ([r]₃ _ _ r)))

`rec⁻¹^sn : ∀ {σ Γ ze su t i} → Γ ⊢sn σ ∋ `rec ze su t < i →
  Γ ⊢sn σ ∋ ze < i × (σ ∷ ℕ ∷ Γ) ⊢sn σ ∋ su < i × Γ ⊢sn ℕ ∋ t < i
`rec⁻¹^sn r^sn = `rec₁⁻¹^sn r^sn , `rec₂⁻¹^sn r^sn , `rec₃⁻¹^sn r^sn

-- Evaluation contexts indexed by the Scope, the type of the hole, and the
-- type of the overall expression.

infix 3 _∣_⊢_ _∣_⊢[_]_∋_<_ _∣_⊢[_]_∋_ _∣_⊢sn_∋_
data _∣_⊢_ Γ α : Type → Set where
  <>  : Γ ∣ α ⊢ α
  app : ∀ {σ τ} → Γ ∣ α ⊢ σ ⇒ τ → Term σ Γ → Γ ∣ α ⊢ τ
  cas : ∀ {σ τ ν} → Γ ∣ α ⊢ σ + τ → Term ν (σ ∷ Γ) → Term ν (τ ∷ Γ) → Γ ∣ α ⊢ ν
  rec : ∀ {σ} → Term σ Γ → Term σ (σ ∷ ℕ ∷ Γ) → Γ ∣ α ⊢ ℕ → Γ ∣ α ⊢ σ

data _∣_⊢[_]_∋_<_ Γ α (R : ∀ Γ σ → Term σ Γ → Size → Set) : ∀ σ → Γ ∣ α ⊢ σ → Size → Set where
  <>  : ∀ {i} → Γ ∣ α ⊢[ R ] α ∋ <> < ↑ i
  app : ∀ {i σ τ c t} → Γ ∣ α ⊢[ R ] σ ⇒ τ ∋ c < i → R Γ σ t i → Γ ∣ α ⊢[ R ] τ ∋ app c t < ↑ i
  cas : ∀ {i σ τ ν c l r} → Γ ∣ α ⊢[ R ] σ + τ ∋ c < i →
        R (σ ∷ Γ) ν l i → R (τ ∷ Γ) ν r i → Γ ∣ α ⊢[ R ] ν ∋ cas c l r < ↑ i
  rec : ∀ {σ ze su c i} → R Γ σ ze i → R (σ ∷ ℕ ∷ Γ) σ su i →
        Γ ∣ α ⊢[ R ] ℕ ∋ c < i → Γ ∣ α ⊢[ R ] σ ∋ rec ze su c < ↑ i

_∣_⊢[_]_∋_ = _∣_⊢[_]_∋_< _
_∣_⊢sn_∋_ = _∣_⊢[ _⊢sn_∋_<_ ]_∋_

cut : ∀ {Γ α σ} → Term α Γ → Γ ∣ α ⊢ σ → Term σ Γ
cut t <>            = t
cut t (app c u)     = cut t c `∙ u
cut t (cas c l r)   = `case (cut t c) l r
cut t (rec ze su c) = `rec ze su (cut t c)

-- Lemma 4.5 Multi-step Reductions with Evaluation Contexts
cut^↝ : ∀ {Γ α σ t u} c → Γ ⊢ α ∋ t ↝ u → Γ ⊢ σ ∋ cut t c ↝ cut u c
cut^↝ <>            red = red
cut^↝ (app c t)     red = [∙]₂ (cut^↝ c red) t
cut^↝ (cas c l r)   red = [c]₁ (cut^↝ c red) l r
cut^↝ (rec ze su c) red = [r]₃ ze su (cut^↝ c red)

cut^↝⋆ : ∀ {Γ α σ t u} c → Γ ⊢ α ∋ t ↝⋆ u → Γ ⊢ σ ∋ cut t c ↝⋆ cut u c
cut^↝⋆ c = S.gmap (flip cut c) (cut^↝ c)

-- Lemma 4.6 Evaluation Contexts
-- Neutrality in the sense of Girard: not (value constructor)-headed
data Neutral {Γ σ} : Term σ Γ → Set where
  var : ∀ v → Neutral (`var v)
  app : ∀ {τ} f (t : Term τ Γ) → Neutral (f `∙ t)
  cas : ∀ {σ τ} (t : Term (σ + τ) Γ) l r → Neutral (`case t l r)
  rec : ∀ ze su t → Neutral (`rec ze su t)

cut⁻¹‿sn^↝ : ∀ {Γ α σ u c t} → Γ ∣ α ⊢sn σ ∋ c → Neutral t → Γ ⊢ σ ∋ cut t c ↝ u →
               (∃ λ t′ → u ≡ cut t′ c × Γ ⊢ α ∋ t ↝ t′)
             ⊎ (∃ λ c′ → u ≡ cut t c′ × Γ ∣ α ⊢sn σ ∋ c′
               × ∀ t′ → Γ ⊢ σ ∋ cut t′ c ↝ cut t′ c′)
-- reduction in the plugged subterm
cut⁻¹‿sn^↝ <> ne r = inj₁ (_ , refl , r)
-- no redexes at the interface thanks to Girard neutrality
cut⁻¹‿sn^↝ (app <> t^sn)        () (β b t)
cut⁻¹‿sn^↝ (cas <> l^sn r^sn)   () (ι₁ t l r)
cut⁻¹‿sn^↝ (cas <> l^sn r^sn)   () (ι₂ t l r)
cut⁻¹‿sn^↝ (rec ze^sn su^sn <>) () (ιz ze su)
cut⁻¹‿sn^↝ (rec ze^sn su^sn <>) () (ιs ze su t)
-- reduction in the context
cut⁻¹‿sn^↝ (app c^sn t^sn) ne ([∙]₁ _ r) =
  inj₂ (_ , refl , app c^sn (Closed-sn t^sn r) , λ u → [∙]₁ _ r)
cut⁻¹‿sn^↝ (cas c^sn l^sn r^sn) ne ([c]₂ t red r) =
  inj₂ (cas _ _ r , refl , cas c^sn (Closed-sn l^sn red) r^sn , λ u → [c]₂ _ red r)
cut⁻¹‿sn^↝ (cas c^sn l^sn r^sn) ne ([c]₃ t l red) =
  inj₂ (cas _ l _ , refl , cas c^sn l^sn (Closed-sn r^sn red) , λ u → [c]₃ _ l red)
cut⁻¹‿sn^↝ (rec ze^sn su^sn c^sn) ne ([r]₁ red su t) =
  inj₂ (rec _ su _ , refl , rec (Closed-sn ze^sn red) su^sn c^sn , λ u → [r]₁ red su _)
cut⁻¹‿sn^↝ (rec ze^sn su^sn c^sn) ne ([r]₂ ze red t) =
  inj₂ (rec ze _ _ , refl , rec ze^sn (Closed-sn su^sn red) c^sn , λ u → [r]₂ ze red _)
-- structural cases: reduction happens deeper
cut⁻¹‿sn^↝ (app c^sn t^sn) ne ([∙]₂ r t) with cut⁻¹‿sn^↝ c^sn ne r
... | inj₁ (t′ , eq , r′)         = inj₁ (t′ , cong (_`∙ t) eq , r′)
... | inj₂ (c′ , eq , c′^sn , r′) =
  inj₂ (app c′ t , cong (_`∙ t) eq , app c′^sn t^sn , λ u → [∙]₂ (r′ u) t)
cut⁻¹‿sn^↝ (cas c^sn l^sn r^sn) ne ([c]₁ red l r) with cut⁻¹‿sn^↝ c^sn ne red
... | inj₁ (t′ , eq , r′)         = inj₁ (t′ , cong (λ t → `case t l r) eq , r′)
... | inj₂ (c′ , eq , c′^sn , r′) =
  inj₂ (_ , cong (λ t → `case t l r) eq , cas c′^sn l^sn r^sn , λ u → [c]₁ (r′ u) l r)
cut⁻¹‿sn^↝ (rec ze^sn su^sn c^sn) ne ([r]₃ ze su red) with cut⁻¹‿sn^↝ c^sn ne red
... | inj₁ (t′ , eq , r′)         = inj₁ (t′ , cong (`rec ze su) eq , r′)
... | inj₂ (c′ , eq , c′^sn , r′) =
  inj₂ (_ , cong (`rec ze su) eq , rec ze^sn su^sn c′^sn , (λ u → [r]₃ _ _ (r′ u)))

cut⁻¹^↝ : ∀ {Γ α σ u} c {v : Var α Γ} → Γ ⊢ σ ∋ cut (`var v) c ↝ u →
          ∃ λ c′ → u ≡ cut (`var v) c′
cut⁻¹^↝ (app <> t)     ([∙]₁ _ r)   = app <> _ , refl
cut⁻¹^↝ (app c t)      ([∙]₁ _ r)   = app c _ , refl
cut⁻¹^↝ (app c t)      ([∙]₂ r _)   =
  let (c′ , eq) = cut⁻¹^↝ c r in app c′ _ , cong (_`∙ _) eq
cut⁻¹^↝ (cas <> l r)   ([c]₂ _ _ _) = cas <> _ _ , refl
cut⁻¹^↝ (cas <> l r)   ([c]₃ _ _ _) = cas <> _ _ , refl
cut⁻¹^↝ (cas c _ _)    ([c]₁ r _ _) =
  let (c′ , eq) = cut⁻¹^↝ c r in cas c′ _ _ , cong (λ c → `case c _ _) eq
cut⁻¹^↝ (cas c l r)    ([c]₂ _ _ _) = cas c _ _ , refl
cut⁻¹^↝ (cas c l r)    ([c]₃ _ _ _) = cas c _ _ , refl
cut⁻¹^↝ (rec ze su <>) ([r]₁ _ _ _) = rec _ _ <> , refl
cut⁻¹^↝ (rec ze su <>) ([r]₂ _ _ _) = rec _ _ <> , refl
cut⁻¹^↝ (rec ze su c)  ([r]₁ _ _ _) = rec _ _ c , refl
cut⁻¹^↝ (rec ze su c)  ([r]₂ _ _ _) = rec _ _ c , refl
cut⁻¹^↝ (rec ze su c)  ([r]₃ _ _ r) =
  let (c′ , eq) = cut⁻¹^↝ c r in rec _ _ c′ , cong (`rec _ _) eq
cut⁻¹^↝ <>             ()


cut⁻¹^sn : ∀ {Γ α σ} t c → Γ ⊢sn σ ∋ cut t c → (Γ ∣ α ⊢sn σ ∋ c) × (Γ ⊢sn α ∋ t)
cut⁻¹^sn t <>        t^sn     = <> , t^sn
cut⁻¹^sn t (app c u) c[t]u^sn =
  let (c[t]^sn , u^sn) = `∙⁻¹^sn c[t]u^sn in
  let (c^sn , t^sn) = cut⁻¹^sn t c c[t]^sn in app c^sn u^sn , t^sn
cut⁻¹^sn t (cas c l r) c[t]lr^sn =
  let (c[t]^sn , l^sn , r^sn) = `case⁻¹^sn c[t]lr^sn in
  let (c^sn , t^sn) = cut⁻¹^sn t c c[t]^sn in cas c^sn l^sn r^sn , t^sn
cut⁻¹^sn t (rec su ze c) zsc[t]^sn =
  let (z^sn , s^sn , c[t]^sn) = `rec⁻¹^sn zsc[t]^sn in
  let (c^sn , t^sn) = cut⁻¹^sn t c c[t]^sn in rec z^sn s^sn c^sn , t^sn

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

-- 3.
`rec^sne : ∀ {Γ α σ ze su} {v : Var α Γ} c → Γ ⊢sn ℕ ∋ cut (`var v) c →
  Γ ⊢sn σ ∋ ze → σ ∷ ℕ ∷ Γ ⊢sn σ ∋ su → Γ ⊢sn σ ∋ cut (`var v) (rec ze su c)
`rec^sne c n^sn ze^sn su^sn = sn (go c n^sn ze^sn su^sn) where

  go : ∀ {Γ α σ ze su} {v : Var α Γ} c → Γ ⊢sn ℕ ∋ cut (`var v) c → Γ ⊢sn σ ∋ ze →
       σ ∷ ℕ ∷ Γ ⊢sn σ ∋ su → Closed (Γ ⊢ σ ∋_↝_) (Γ ⊢sn σ ∋_) (cut (`var v) (rec ze su c))
  go <> n^sne      ze^sn      su^sn      ([r]₃ _ _ ())
  go c  n^sne      (sn ze^sn) su^sn      ([r]₁ red _ _) = sn (go c n^sne (ze^sn red) su^sn)
  go c  n^sne      ze^sn      (sn su^sn) ([r]₂ _ red _) = sn (go c n^sne ze^sn (su^sn red))
  go c  (sn n^sne) ze^sn      su^sn      ([r]₃ _ _ red) =
    let (c′ , eq) = cut⁻¹^↝ c red in let red′ = subst (_ ⊢ _ ∋ _ ↝_) eq red in
    subst (λ g → _ ⊢sn _ ∋ `rec _ _ g) (sym eq) (sn (go c′ (n^sne red′) ze^sn su^sn))

cut^sn : ∀ {Γ α σ} v {c} → Γ ∣ α ⊢sn σ ∋ c → Γ ⊢sn σ ∋ cut (`var v) c
cut^sn v               <>                     = `var^sne v
cut^sn v {app c t}     (app c^sn t^sn)        = `∙^sne c (cut^sn v c^sn) t^sn
cut^sn v {cas c l r}   (cas c^sn l^sn r^sn)   = `case^sne c (cut^sn v c^sn) l^sn r^sn
cut^sn v {rec ze su c} (rec ze^sn su^sn c^sn) = `rec^sne c (cut^sn v c^sn) ze^sn su^sn

-- Lemma 4.8 Composition of evaluation contexts
_∘C_ : ∀ {Γ α β σ} → Γ ∣ β ⊢ σ → Γ ∣ α ⊢ β → Γ ∣ α ⊢ σ
<>          ∘C c′ = c′
app c t     ∘C c′ = app (c ∘C c′) t
cas c l r   ∘C c′ = cas (c ∘C c′) l r
rec ze su c ∘C c′ = rec ze su (c ∘C c′)

cut-∘C : ∀ {Γ α β σ} t (c : Γ ∣ β ⊢ σ) (c′ : Γ ∣ α ⊢ β) →
         cut (cut t c′) c ≡ cut t (c ∘C c′)
cut-∘C t <>            c′ = refl
cut-∘C t (app c u)     c′ = cong (_`∙ u) (cut-∘C t c c′)
cut-∘C t (cas c l r)   c′ = cong (λ t → `case t l r) (cut-∘C t c c′)
cut-∘C t (rec ze su c) c′ = cong (`rec ze su) (cut-∘C t c c′)

∘C^R : ∀ {Γ α R β σ c c′} → Γ ∣ β ⊢[ R ] σ ∋ c → Γ ∣ α ⊢[ R ] β ∋ c′ → Γ ∣ α ⊢[ R ] σ ∋ c ∘C c′
∘C^R <>                  c′^R = c′^R
∘C^R (app c^R t^R)       c′^R = app (∘C^R c^R c′^R) t^R
∘C^R (cas c^R l^R r^R)   c′^R = cas (∘C^R c^R c′^R) l^R r^R
∘C^R (rec ze^R su^R c^R) c′^R = rec ze^R su^R (∘C^R c^R c′^R)

-- β or ι redexes
infix 3 _⊢↯_ _⊢↯sn_∋_
data _⊢↯_ (Γ : List Type) (τ : Type) : Set where
  β  : ∀ {σ}     → Term τ (σ ∷ Γ) → Term σ Γ → Γ ⊢↯ τ
  ι₁ : ∀ {σ₁ σ₂} → Term σ₁ Γ → Term τ (σ₁ ∷ Γ) → Term τ (σ₂ ∷ Γ) → Γ ⊢↯ τ
  ι₂ : ∀ {σ₁ σ₂} → Term σ₂ Γ → Term τ (σ₁ ∷ Γ) → Term τ (σ₂ ∷ Γ) → Γ ⊢↯ τ
  ιz : Term τ Γ → Term τ (τ ∷ ℕ ∷ Γ) → Γ ⊢↯ τ
  ιs : Term τ Γ → Term τ (τ ∷ ℕ ∷ Γ) → Term ℕ Γ → Γ ⊢↯ τ

-- Notion of sn for redexes: all the redex's components are sn
-- We defined this one by case analysis on Γ ⊢↯ τ because that seems to be easier
-- on the termination checker.
_⊢↯sn_∋_ : ∀ Γ τ → Γ ⊢↯ τ → Set
Γ ⊢↯sn τ ∋ β b u      = (_ ∷ Γ) ⊢sn τ ∋ b × Γ ⊢sn _ ∋ u
Γ ⊢↯sn τ ∋ ι₁ t l r   = Γ ⊢sn _ ∋ t × (_ ∷ Γ) ⊢sn _ ∋ l × (_ ∷ Γ) ⊢sn _ ∋ r
Γ ⊢↯sn τ ∋ ι₂ t l r   = Γ ⊢sn _ ∋ t × (_ ∷ Γ) ⊢sn _ ∋ l × (_ ∷ Γ) ⊢sn _ ∋ r
Γ ⊢↯sn τ ∋ ιz ze su   = Γ ⊢sn τ ∋ ze × (τ ∷ ℕ ∷ Γ) ⊢sn τ ∋ su
Γ ⊢↯sn τ ∋ ιs ze su t = Γ ⊢sn τ ∋ ze × (τ ∷ ℕ ∷ Γ) ⊢sn τ ∋ su × Γ ⊢sn ℕ ∋ t

-- Pre and Post firing of the redex.
-- * Pre-firing we have a Girard-neutral.
-- * Pre and Post are naturally linked via Typed Reduction as fire demonstrates
unRed : ∀ {Γ τ} → Γ ⊢↯ τ → Term τ Γ
unRed (β b u)      = `λ b `∙ u
unRed (ι₁ t l r)   = `case (`i₁ t) l r
unRed (ι₂ t l r)   = `case (`i₂ t) l r
unRed (ιz ze su)   = `rec ze su `0
unRed (ιs ze su t) = `rec ze su (`1+ t)

unRed^Neutral : ∀ {Γ τ} (r : Γ ⊢↯ τ) → Neutral (unRed r)
unRed^Neutral (β b u)      = app (`λ b) u
unRed^Neutral (ι₁ t l r)   = cas (`i₁ t) l r
unRed^Neutral (ι₂ t l r)   = cas (`i₂ t) l r
unRed^Neutral (ιz ze su)   = rec ze su `0
unRed^Neutral (ιs ze su t) = rec ze su (`1+ t)

βιRed : ∀ {Γ τ} → Γ ⊢↯ τ → Term τ Γ
βιRed (β b u)      = b [ u /0]
βιRed (ι₁ t l r)   = l [ t /0]
βιRed (ι₂ t l r)   = r [ t /0]
βιRed (ιz ze su)   = ze
βιRed (ιs ze su t) = sub (base vl^Tm ∙ t ∙ `rec ze su t) su

fire : ∀ {Γ τ} r → Γ ⊢ τ ∋ unRed r ↝ βιRed r
fire (β b u)      = β b u
fire (ι₁ t l r)   = ι₁ t l r
fire (ι₂ t l r)   = ι₂ t l r
fire (ιz ze su)   = ιz ze su
fire (ιs ze su t) = ιs ze su t

-- Closure under fire-expansion
c[fire]⁻¹^Closed-sn : ∀ {Γ α σ c} r → Γ ⊢↯sn α ∋ r → Γ ∣ α ⊢sn σ ∋ c →
  Γ ⊢sn σ ∋ cut (βιRed r) c → Closed (Γ ⊢ σ ∋_↝_) (Γ ⊢sn σ ∋_) (cut (unRed r) c)
c[fire⁻¹]^Closed-sn : ∀ {Γ α σ} c r → Γ ⊢↯sn α ∋ r → Γ ∣ α ⊢sn σ ∋ c →
  Γ ⊢sn σ ∋ cut (βιRed r) c → ∀ {t} → Γ ⊢ α ∋ unRed r ↝ t → Γ ⊢sn σ ∋ cut t c

c[fire]⁻¹^Closed-sn r r^sn c^sn c[r]^sn@(sn c[r]^sn′) red
  with cut⁻¹‿sn^↝ c^sn (unRed^Neutral r) red
... | inj₁ (_ , refl , r′) = c[fire⁻¹]^Closed-sn _ r r^sn c^sn c[r]^sn r′
... | inj₂ (c′ , refl , c′^sn , red′) =
  sn (c[fire]⁻¹^Closed-sn r r^sn c′^sn (c[r]^sn′ (red′ (βιRed r))))

-- Either the redex does fire
c[fire⁻¹]^Closed-sn c (β _ _)    _ c^sn c[r]^sn (β _ _)    = c[r]^sn
c[fire⁻¹]^Closed-sn c (ι₁ _ _ _) _ c^sn c[r]^sn (ι₁ _ _ _) = c[r]^sn
c[fire⁻¹]^Closed-sn c (ι₂ _ _ _) _ c^sn c[r]^sn (ι₂ _ _ _) = c[r]^sn
c[fire⁻¹]^Closed-sn c (ιz _ _)   _ c^sn c[r]^sn (ιz _ _)   = c[r]^sn
c[fire⁻¹]^Closed-sn c (ιs _ _ _) _ c^sn c[r]^sn (ιs _ _ _) = c[r]^sn

-- Or we are in a structural case
-- β redex
c[fire⁻¹]^Closed-sn c (β b u) (b^sn , sn u^sn) c^sn c[r]^sn ([∙]₁ _ red) =
  let c[r′]^sn = Closed⋆-sn c[r]^sn (cut^↝⋆ c ([/0]^↝⋆ b red)) in
  sn (c[fire]⁻¹^Closed-sn (β b _) (b^sn , u^sn red) c^sn c[r′]^sn)
c[fire⁻¹]^Closed-sn c (β b u) (sn b^sn , u^sn) c^sn c[r]^sn ([∙]₂ ([λ] red) t) =
  let c[r′]^sn = Closed-sn c[r]^sn (cut^↝ c ([/0]^↝ red u)) in
  sn (c[fire]⁻¹^Closed-sn (β _ u) (b^sn red , u^sn) c^sn c[r′]^sn)

-- ι₁ redex
c[fire⁻¹]^Closed-sn c (ι₁ t l r) (sn t^sn , l^sn , r^sn) c^sn c[r]^sn ([c]₁ ([i₁] red) _ _) =
  let c[r′]^sn = Closed⋆-sn c[r]^sn (cut^↝⋆ c ([/0]^↝⋆ l red)) in
  sn (c[fire]⁻¹^Closed-sn (ι₁ _ l r) (t^sn red , l^sn , r^sn) c^sn c[r′]^sn)
c[fire⁻¹]^Closed-sn c (ι₁ t l r) (t^sn , sn l^sn , r^sn) c^sn c[r]^sn ([c]₂ _ red _) =
  let c[r′]^sn = Closed-sn c[r]^sn (cut^↝ c ([/0]^↝ red t)) in
  sn (c[fire]⁻¹^Closed-sn (ι₁ t _ r) (t^sn , l^sn red , r^sn) c^sn c[r′]^sn)
c[fire⁻¹]^Closed-sn c (ι₁ t l r) (t^sn , l^sn , sn r^sn) c^sn c[r]^sn ([c]₃ _ _ red) =
  sn (c[fire]⁻¹^Closed-sn (ι₁ t l _) (t^sn , l^sn , r^sn red) c^sn c[r]^sn)

-- ι₂ redex
c[fire⁻¹]^Closed-sn c (ι₂ t l r) (sn t^sn , l^sn , r^sn) c^sn c[r]^sn ([c]₁ ([i₂] red) _ _) =
  let c[r′]^sn = Closed⋆-sn c[r]^sn (cut^↝⋆ c ([/0]^↝⋆ r red)) in
  sn (c[fire]⁻¹^Closed-sn (ι₂ _ l r) (t^sn red , l^sn , r^sn) c^sn c[r′]^sn)
c[fire⁻¹]^Closed-sn c (ι₂ t l r) (t^sn , sn l^sn , r^sn) c^sn c[r]^sn ([c]₂ _ red _) =
  sn (c[fire]⁻¹^Closed-sn (ι₂ t _ r) (t^sn , l^sn red , r^sn) c^sn c[r]^sn)
c[fire⁻¹]^Closed-sn c (ι₂ t l r) (t^sn , l^sn , sn r^sn) c^sn c[r]^sn ([c]₃ _ _ red) =
  let c[r′]^sn = Closed-sn c[r]^sn (cut^↝ c ([/0]^↝ red t)) in
  sn (c[fire]⁻¹^Closed-sn (ι₂ t l _) (t^sn , l^sn , r^sn red) c^sn c[r′]^sn)

-- ιz redex
c[fire⁻¹]^Closed-sn c (ιz ze su) (sn ze^sn , su^sn) c^sn c[r]^sn ([r]₁ red _ _) =
  let c[r′]^sn = Closed-sn c[r]^sn (cut^↝ c red) in
  sn (c[fire]⁻¹^Closed-sn (ιz _ su) (ze^sn red , su^sn) c^sn c[r′]^sn)
c[fire⁻¹]^Closed-sn c (ιz ze su) (ze^sn , sn su^sn) c^sn c[r]^sn ([r]₂ _ red _) =
  sn (c[fire]⁻¹^Closed-sn (ιz ze _) (ze^sn , su^sn red) c^sn c[r]^sn)
c[fire⁻¹]^Closed-sn c (ιz ze su) _ c^sn c[r]^sn ([r]₃ _ _ ())

-- ιs redex
c[fire⁻¹]^Closed-sn c (ιs ze su t) (sn ze^sn , su^sn , t^sn) c^sn c[r]^sn ([r]₁ red _ _) =
  let reds = sub^↝⋆ su ([v↦t↝⋆t] ∙^R S.ε ∙^R S.return ([r]₁ red _ _)) in
  let c[r′]^sn = Closed⋆-sn c[r]^sn (cut^↝⋆ c reds) in
  sn (c[fire]⁻¹^Closed-sn (ιs _ su t) (ze^sn red , su^sn , t^sn) c^sn c[r′]^sn)
c[fire⁻¹]^Closed-sn c (ιs ze su t) (ze^sn , sn su^sn , t^sn) c^sn c[r]^sn ([r]₂ _ red _) =
  let reds = S.return (sub^↝ (base vl^Tm ∙ t ∙ `rec ze su t) red)
             S.◅◅ sub^↝⋆ (tgt red) ([v↦t↝⋆t] ∙^R S.ε ∙^R S.return ([r]₂ _ red _)) in
  let c[r′]^sn = Closed⋆-sn c[r]^sn (cut^↝⋆ c reds) in
  sn (c[fire]⁻¹^Closed-sn (ιs ze _ t) (ze^sn , su^sn red , t^sn) c^sn c[r′]^sn)
c[fire⁻¹]^Closed-sn c (ιs ze su t) (ze^sn , su^sn , sn t^sn) c^sn c[r]^sn ([r]₃ _ _ ([1+] red)) =
  let reds = sub^↝⋆ su ([v↦t↝⋆t] ∙^R S.return red ∙^R S.return ([r]₃ _ _ red)) in
  let c[r′]^sn = Closed⋆-sn c[r]^sn (cut^↝⋆ c reds) in
  sn (c[fire]⁻¹^Closed-sn (ιs ze su _) (ze^sn , su^sn , t^sn red) c^sn c[r′]^sn)

c[fire⁻¹]^sn : ∀ {Γ α σ c} r → Γ ⊢↯sn α ∋ r → Γ ∣ α ⊢sn σ ∋ c →
               Γ ⊢sn σ ∋ cut (βιRed r) c → Γ ⊢sn σ ∋ cut (unRed r) c
c[fire⁻¹]^sn r r^sn c^sn c[r]^sn = sn (c[fire]⁻¹^Closed-sn r r^sn c^sn c[r]^sn)

-- Section 3.2 Inductive Definition of Strongly Normalizing Terms
-- TODO: refactor computational part as: Γ ⊢↯ τ + R-constraints?
infix 4 _⊢[_]_∋_↝_<_
data _⊢[_]_∋_↝_<_ Γ (R : ∀ Γ σ → Term σ Γ → Size → Set) τ : (t u : Term τ Γ) → Size → Set where
-- computational
  β    : ∀ {σ i} t u → R Γ σ u i → Γ ⊢[ R ] τ ∋ `λ t `∙ u ↝ t [ u /0] < ↑ i
  ι₁   : ∀ {σ₁ σ₂ i} t l r → R Γ σ₁ t i → R (σ₂ ∷ Γ) τ r i →
         Γ ⊢[ R ] τ ∋ `case (`i₁ t) l r ↝ l [ t /0] < ↑ i
  ι₂   : ∀ {σ₁ σ₂ i} t l r → R Γ σ₂ t i → R (σ₁ ∷ Γ) τ l i →
         Γ ⊢[ R ] τ ∋ `case (`i₂ t) l r ↝ r [ t /0] < ↑ i
  ιz   : ∀ {i} ze su → R (τ ∷ ℕ ∷ Γ) τ su i → Γ ⊢[ R ] τ ∋ `rec ze su `0 ↝ ze < ↑ i
  ιs   : ∀ {i} ze su t → R Γ τ ze i → R Γ ℕ t i →
         Γ ⊢[ R ] τ ∋ `rec ze su (`1+ t) ↝ sub (base vl^Tm ∙ t ∙ `rec ze su t) su < ↑ i
-- structural
  [∙]₂ : ∀ {σ i f g} → Γ ⊢[ R ] σ ⇒ τ ∋ f ↝ g < i → ∀ t → Γ ⊢[ R ] τ ∋ f `∙ t ↝ g `∙ t < ↑ i
  [c]₁ : ∀ {σ₁ σ₂ i t u} → Γ ⊢[ R ] σ₁ + σ₂ ∋ t ↝ u < i → ∀ l r →
         Γ ⊢[ R ] τ ∋ `case t l r ↝ `case u l r < ↑ i
  [r]₃ : ∀ {i t u} ze su → Γ ⊢[ R ] ℕ ∋ t ↝ u < i →
         Γ ⊢[ R ] τ ∋ `rec ze su t ↝ `rec ze su u < ↑ i

infix 4 _⊢_∋_↝SN_<_ _⊢SN_∋_<_ _⊢SNe_∋_<_ _⊢_∋_↝SN_ _⊢SN_∋_ _⊢SNe_∋_
_⊢_∋_↝SN_<_ : ∀ Γ τ (t u : Term τ Γ) → Size → Set
data _⊢SN_∋_<_ (Γ : List Type) : (σ : Type) → Term σ Γ → Size → Set
data _⊢SNe_∋_<_ (Γ : List Type) : (σ : Type) → Term σ Γ → Size → Set

_⊢_∋_↝SN_<_ = _⊢[ _⊢SN_∋_<_ ]_∋_↝_<_

data _⊢SN_∋_<_ Γ where
  neu : ∀ {σ t i} → Γ ⊢SNe σ ∋ t < i → Γ ⊢SN σ ∋ t < ↑ i
  lam : ∀ {σ τ b i} → (σ ∷ Γ) ⊢SN τ ∋ b < i → Γ ⊢SN σ ⇒ τ ∋ `λ b < ↑ i
  inl : ∀ {σ τ t i} → Γ ⊢SN σ ∋ t < i → Γ ⊢SN σ + τ ∋ `i₁ t < ↑ i
  inr : ∀ {σ τ t i} → Γ ⊢SN τ ∋ t < i → Γ ⊢SN σ + τ ∋ `i₂ t < ↑ i
  zro : ∀ {i} → Γ ⊢SN ℕ ∋ `0 < ↑ i
  suc : ∀ {i t} → Γ ⊢SN ℕ ∋ t < i → Γ ⊢SN ℕ ∋ `1+ t < ↑ i
  red : ∀ {σ t t′ i} → Γ ⊢ σ ∋ t ↝SN t′ < i → Γ ⊢SN σ ∋ t′ < i → Γ ⊢SN σ ∋ t < ↑ i

data _⊢SNe_∋_<_ Γ where
  var : ∀ {σ i} v → Γ ⊢SNe σ ∋ `var v < ↑ i
  app : ∀ {σ τ f t i} → Γ ⊢SNe σ ⇒ τ ∋ f < i → Γ ⊢SN σ ∋ t < i → Γ ⊢SNe τ ∋ f `∙ t < ↑ i
  cas : ∀ {σ τ ν t l r i} → Γ ⊢SNe σ + τ ∋ t < i →
        (σ ∷ Γ) ⊢SN ν ∋ l < i → (τ ∷ Γ) ⊢SN ν ∋ r < i → Γ ⊢SNe ν ∋ `case t l r < ↑ i
  rec : ∀ {σ i ze su t} → Γ ⊢SN σ ∋ ze < i → (σ ∷ ℕ ∷ Γ) ⊢SN σ ∋ su < i →
        Γ ⊢SNe ℕ ∋ t < i → Γ ⊢SNe σ ∋ `rec ze su t < ↑ i

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
_∣_⊢SN_∋_<_ = _∣_⊢[ _⊢SN_∋_<_ ]_∋_<_
_∣_⊢SN_∋_ = _∣_⊢SN_∋_< _

cut⁻¹^SNe : ∀ {Γ τ t i} → Γ ⊢SNe τ ∋ t < i →
  Σ[ ctx ∈ (∃ λ σ → Γ ∣ σ ⊢ τ) ] let (σ , c) = ctx in
            ∃ λ v → t ≡ cut (`var v) c × Γ ∣ σ ⊢SN τ ∋ c < i
cut⁻¹^SNe (var v)          = _ , v , refl , <>
cut⁻¹^SNe (app f^SNe t^SN) =
  let (_ , v , eq , c^SN) = cut⁻¹^SNe f^SNe
  in _ , v , cong (_`∙ _) eq , app c^SN t^SN
cut⁻¹^SNe (cas t^SNe l^SN r^SN) =
  let (_ , v , eq , c^SN) = cut⁻¹^SNe t^SNe
  in _ , v , cong (λ t → `case t _ _) eq , cas c^SN l^SN r^SN
cut⁻¹^SNe (rec ze^SN su^SN t^SNe) =
  let (_ , v , eq , c^SN) = cut⁻¹^SNe t^SNe
  in _ , v , cong (`rec _ _) eq , rec ze^SN su^SN c^SN

-- Lemma 4.11 Thinning
mutual

 -- 1.
 th^SN : ∀ {σ Γ Δ t} ρ → Γ ⊢SN σ ∋ t → Δ ⊢SN σ ∋ ren ρ t
 th^SN ρ (neu n)   = neu (th^SNe ρ n)
 th^SN ρ (lam t)   = lam (th^SN _ t)
 th^SN ρ (inl t)   = inl (th^SN ρ t)
 th^SN ρ (inr t)   = inr (th^SN ρ t)
 th^SN ρ zro       = zro
 th^SN ρ (suc t)   = suc (th^SN ρ t)
 th^SN ρ (red r t) = red (th^↝SN ρ r) (th^SN ρ t)

 -- 2.
 th^SNe : ∀ {σ Γ Δ t} ρ → Γ ⊢SNe σ ∋ t → Δ ⊢SNe σ ∋ ren ρ t
 th^SNe ρ (var v)       = var (lookup ρ v)
 th^SNe ρ (app n t)     = app (th^SNe ρ n) (th^SN ρ t)
 th^SNe ρ (cas n l r)   = cas (th^SNe ρ n) (th^SN _ l) (th^SN _ r)
 th^SNe ρ (rec ze su t) = rec (th^SN ρ ze) (th^SN _ su) (th^SNe ρ t)

 -- 3.
 th^↝SN : ∀ {σ Γ Δ t u} ρ → Γ ⊢ σ ∋ t ↝SN u → Δ ⊢ σ ∋ ren ρ t ↝SN ren ρ u
 -- computational
 th^↝SN ρ (β t u u^SN)            =
   subst (_ ⊢ _ ∋ ren ρ (`λ t `∙ u) ↝SN_< _) (renβ TermD t (ε ∙ u) ρ) (β _ (ren ρ u) (th^SN ρ u^SN))
 th^↝SN ρ (ι₁ t l r t^SN r^SN)    =
   subst (_ ⊢ _ ∋ ren ρ (`case (`i₁ t) l r) ↝SN_< _) (renβ TermD l (ε ∙ t) ρ)
   $ ι₁ _ _ (ren _ r) (th^SN ρ t^SN) (th^SN _ r^SN)
 th^↝SN ρ (ι₂ t l r t^SN l^SN)    =
   subst (_ ⊢ _ ∋ ren ρ (`case (`i₂ t) l r) ↝SN_< _) (renβ TermD r (ε ∙ t) ρ)
   $ ι₂ _ (ren _ l) _ (th^SN ρ t^SN) (th^SN _ l^SN)
 th^↝SN ρ (ιz ze su su^SN)        = ιz (ren ρ ze) (ren _ su) (th^SN _ su^SN)
 th^↝SN ρ (ιs ze su t ze^SN t^SN) =
   subst (_ ⊢ _ ∋ ren ρ (`rec ze su (`1+ t)) ↝SN_< _) (renβ TermD su (ε ∙ t ∙ `rec ze su t) ρ)
   $ ιs (ren ρ ze) (ren _ su) (ren ρ t) (th^SN ρ ze^SN) (th^SN ρ t^SN)
 -- structural
 th^↝SN ρ ([∙]₂ r t)     = [∙]₂ (th^↝SN ρ r) (ren ρ t)
 th^↝SN ρ ([c]₁ r bl br) = [c]₁ (th^↝SN ρ r) (ren _ bl) (ren _ br)
 th^↝SN ρ ([r]₃ ze su r) = [r]₃ (ren ρ ze) (ren _ su) (th^↝SN ρ r)

freshˡ^SNe : ∀ {Γ Δ} → pred.∀[ SNe ] (freshˡ vl^Tm Δ {Γ})
lookup^P freshˡ^SNe k = th^SNe (pack (injectˡ _)) (cast (var k))
  where cast = subst (_ ⊢SNe _ ∋_) (sym (lookup-base^Tm k))

-- Lemma 4.12 Anti-Thinning
mutual

 -- 1.
 th⁻¹^SN : ∀ {σ Γ Δ t′} t ρ → t′ ≡ ren ρ t → Δ ⊢SN σ ∋ t′ → Γ ⊢SN σ ∋ t
 th⁻¹^SN t         ρ eq    (neu pr) = neu (th⁻¹^SNe t ρ eq pr)
 th⁻¹^SN (`λ t)    ρ refl  (lam pr) = lam (th⁻¹^SN t _ refl pr)
 th⁻¹^SN (`i₁ t)   ρ refl  (inl pr) = inl (th⁻¹^SN t ρ refl pr)
 th⁻¹^SN (`i₂ t)   ρ refl  (inr pr) = inr (th⁻¹^SN t ρ refl pr)
 th⁻¹^SN `0        ρ refl  zro      = zro
 th⁻¹^SN (`1+ t)   ρ refl  (suc pr) = suc (th⁻¹^SN t ρ refl pr)
 th⁻¹^SN (`var v)  ρ ()    (lam pr)
 th⁻¹^SN (`var v)  ρ ()    (inl pr)
 th⁻¹^SN (`var v)  ρ ()    (inr pr)
 th⁻¹^SN (`var v)  ρ ()    zro
 th⁻¹^SN (`var v)  ρ ()    (suc pr)
 th⁻¹^SN t         ρ refl  (red r pr)  =
   let (t′ , eq , r′) = th⁻¹^↝SN t ρ r in red r′ (th⁻¹^SN t′ ρ eq pr)

 -- 2.
 th⁻¹^SNe : ∀ {σ Γ Δ t′} t ρ → t′ ≡ ren ρ t → Δ ⊢SNe σ ∋ t′ → Γ ⊢SNe σ ∋ t
 th⁻¹^SNe (`var v) ρ refl (var _)     = var v
 th⁻¹^SNe (f `∙ t) ρ refl (app rf rt) =
   app (th⁻¹^SNe f ρ refl rf) (th⁻¹^SN t ρ refl rt)
 th⁻¹^SNe (`case t l r) ρ refl (cas rt rl rr) =
   cas (th⁻¹^SNe t ρ refl rt) (th⁻¹^SN l _ refl rl) (th⁻¹^SN r _ refl rr)
 th⁻¹^SNe (`rec ze su t) ρ refl (rec rze rsu rt) =
   rec (th⁻¹^SN ze ρ refl rze) (th⁻¹^SN su _ refl rsu) (th⁻¹^SNe t ρ refl rt)

 -- 3.
 th⁻¹^↝SN : ∀ {σ Γ Δ u} t ρ → Δ ⊢ σ ∋ ren ρ t ↝SN u → ∃ λ u′ → u ≡ ren ρ u′ × Γ ⊢ σ ∋ t ↝SN u′
 -- value constructors don't head SN-reduce
 th⁻¹^↝SN (`var v)    ρ ()
 th⁻¹^↝SN (`λ b)      ρ ()
 th⁻¹^↝SN (`i₁ t)     ρ ()
 th⁻¹^↝SN (`i₂ t)     ρ ()
 th⁻¹^↝SN `0          ρ ()
 th⁻¹^↝SN (`1+ t)     ρ ()
 -- reductions
 th⁻¹^↝SN (`λ b `∙ t) ρ (β ._ ._ t^SN) =
   b [ t /0] , renβ TermD b (ε ∙ t) ρ , β b t (th⁻¹^SN t ρ refl t^SN)
 th⁻¹^↝SN (`case (`i₁ t) l r) ρ (ι₁ ._ ._ ._ t^SN r^SN) =
   l [ t /0] , renβ TermD l (ε ∙ t) ρ , ι₁ t l r (th⁻¹^SN t ρ refl t^SN) (th⁻¹^SN r _ refl r^SN)
 th⁻¹^↝SN (`case (`i₂ t) l r) ρ (ι₂ ._ ._ ._ t^SN l^SN) =
   r [ t /0] , renβ TermD r (ε ∙ t) ρ , ι₂ t l r (th⁻¹^SN t ρ refl t^SN) (th⁻¹^SN l _ refl l^SN)
 th⁻¹^↝SN (`rec ze su `0) ρ (ιz _ _ su^SN) = ze , refl , ιz ze su (th⁻¹^SN su _ refl su^SN)
 th⁻¹^↝SN (`rec ze su (`1+ t)) ρ (ιs _ _ _ ze^SN t^SN) =
   sub (base vl^Tm ∙ t ∙ `rec ze su t) su , renβ TermD su (ε ∙ t ∙ `rec ze su t) ρ
   , ιs ze su t (th⁻¹^SN ze ρ refl ze^SN) (th⁻¹^SN t ρ refl t^SN)
-- structural
 th⁻¹^↝SN (f `∙ t)        ρ ([∙]₂ r ._)    =
   let (g , eq , r′) = th⁻¹^↝SN f ρ r in g `∙ t , cong (_`∙ ren ρ t) eq , [∙]₂ r′ t
 th⁻¹^↝SN (`case c bl br) ρ ([c]₁ r ._ ._) = let (d , eq , r′) = th⁻¹^↝SN c ρ r in
   `case d bl br , cong (λ c → `case c (ren _ bl) (ren _ br)) eq , [c]₁ r′ bl br
 th⁻¹^↝SN (`rec ze su t) ρ ([r]₃ ._ ._ r) = let (t′ , eq , r′) = th⁻¹^↝SN t ρ r in
   `rec ze su t′ , cong (`rec (ren ρ ze) (ren _ su)) eq , [r]₃ ze su r′

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
  eq = sym $ Sim.sim Sim.RenSub (base^VarTm^R ∙^R refl) t

-- Section 4.3 Soundness (Short alternative proof)
infix 4 _⊢_∋_↝sn_<_ _⊢_∋_↝sn_
_⊢_∋_↝sn_<_ = _⊢[ _⊢sn_∋_<_ ]_∋_↝_<_
_⊢_∋_↝sn_ = _⊢_∋_↝sn_< _

-- Lemma 4.17 Backwards closure of sn
↝sn⁻¹^sn : ∀ {Γ σ τ t′ t i} c → Γ ⊢ σ ∋ t′ ↝sn t < i →
           Γ ⊢sn τ ∋ cut t c → Γ ⊢sn τ ∋ cut t′ c
-- computational
↝sn⁻¹^sn c (β b u u^sn) c[b[u]]^sn =
  let (c^sn , b[u]^sn) = cut⁻¹^sn (b [ u /0]) c c[b[u]]^sn in
  let b^sn = [/0]⁻¹^sn b u b[u]^sn in
  c[fire⁻¹]^sn (β b u) (b^sn , u^sn) c^sn c[b[u]]^sn
↝sn⁻¹^sn c (ι₁ t l r t^sn r^sn) c[l[t]]^sn =
  let (c^sn , l[t]^sn) = cut⁻¹^sn (l [ t /0]) c c[l[t]]^sn in
  let l^sn = [/0]⁻¹^sn l t l[t]^sn in
  c[fire⁻¹]^sn (ι₁ t l r) (t^sn , l^sn , r^sn) c^sn c[l[t]]^sn
↝sn⁻¹^sn c (ι₂ t l r t^sn l^sn) c[r[t]]^sn =
  let (c^sn , r[t]^sn) = cut⁻¹^sn (r [ t /0]) c c[r[t]]^sn in
  let r^sn = [/0]⁻¹^sn r t r[t]^sn in
  c[fire⁻¹]^sn (ι₂ t l r) (t^sn , l^sn , r^sn) c^sn c[r[t]]^sn
↝sn⁻¹^sn c (ιz ze su su^sn) c[ze]^sn =
  let (c^sn , ze^sn) = cut⁻¹^sn ze c c[ze]^sn in
  c[fire⁻¹]^sn (ιz ze su) (ze^sn , su^sn) c^sn c[ze]^sn
↝sn⁻¹^sn c (ιs ze su t ze^sn t^sn) c[s[zst]]^sn =
  let (c^sn , s[zst]^sn) = cut⁻¹^sn _ c c[s[zst]]^sn in
  let su^sn = sub⁻¹^sn su (base vl^Tm ∙ t ∙ `rec ze su t) s[zst]^sn in
  c[fire⁻¹]^sn (ιs ze su t) (ze^sn , su^sn , t^sn) c^sn c[s[zst]]^sn
-- structural
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
↝sn⁻¹^sn c ([r]₃ ze su r^sn) c[zst]^sn =
  let eq t    = cut-∘C t c (rec ze su <>) in
  let zst^sn′ = subst (_ ⊢sn _ ∋_) (eq _) c[zst]^sn in
  let ih      = ↝sn⁻¹^sn (c ∘C rec ze su <>) r^sn zst^sn′ in
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
 sound^SN zro          = `0^sn
 sound^SN (suc t^SN)   = `1+^sn (sound^SN t^SN)
 sound^SN (red r t^SN) = ↝sn⁻¹^sn <> (sound^↝SN r) (sound^SN t^SN)

 -- 2.
 sound^∣SN : ∀ {Γ α σ c i} → Γ ∣ α ⊢SN σ ∋ c < i → Γ ∣ α ⊢sn σ ∋ c
 sound^∣SN <>                     = <>
 sound^∣SN (app c^SN t^SN)        = app (sound^∣SN c^SN) (sound^SN t^SN)
 sound^∣SN (cas c^SN l^SN r^SN)   = cas (sound^∣SN c^SN) (sound^SN l^SN) (sound^SN r^SN)
 sound^∣SN (rec ze^SN su^SN t^SN) = rec (sound^SN ze^SN) (sound^SN su^SN) (sound^∣SN t^SN)

 -- 3.
 sound^↝SN : ∀ {Γ σ t u i} → Γ ⊢ σ ∋ t ↝SN u < i → Γ ⊢ σ ∋ t ↝sn u
 sound^↝SN (β t u u^SN)            = β t u (sound^SN u^SN)
 sound^↝SN (ι₁ t l r t^SN r^SN)    = ι₁ t l r (sound^SN t^SN) (sound^SN r^SN)
 sound^↝SN (ι₂ t l r t^SN l^SN)    = ι₂ t l r (sound^SN t^SN) (sound^SN l^SN)
 sound^↝SN (ιz ze su su^SN)        = ιz ze su (sound^SN su^SN)
 sound^↝SN (ιs ze su t ze^SN t^SN) = ιs ze su t (sound^SN ze^SN) (sound^SN t^SN)
 sound^↝SN ([∙]₂ r t)              = [∙]₂ (sound^↝SN r) t
 sound^↝SN ([c]₁ r _ _)            = [c]₁ (sound^↝SN r) _ _
 sound^↝SN ([r]₃ _ _ r)            = [r]₃ _ _ (sound^↝SN r)

-- Section 4.4 Soundness and Completeness

-- Theorem 4.16 Completeness of SN
-- We start with a definition of deeply nested β-redexes

data Elim (Γ : List Type) (τ : Type) : Type → Set where
  app : ∀ {σ} → Term σ Γ → Elim Γ τ (σ ⇒ τ)
  cas : ∀ {σ₁ σ₂} → Term τ (σ₁ ∷ Γ) → Term τ (σ₂ ∷ Γ) → Elim Γ τ (σ₁ + σ₂)
  rec : Term τ Γ → Term τ (τ ∷ ℕ ∷ Γ) → Elim Γ τ ℕ

elim : ∀ {Γ σ τ} → Elim Γ τ σ → Γ ∣ σ ⊢ τ
elim (app t)     = app <> t
elim (cas l r)   = cas <> l r
elim (rec ze su) = rec ze su <>

mutual
  -- 1.
  complete^SNe : ∀ {Γ σ α i c} v → Γ ∣ α ⊢SN σ ∋ c →
    let t = cut (`var v) c in ∀ {t′} → t′ ≡ t → Γ ⊢sn σ ∋ t′ < i → Γ ⊢SNe σ ∋ t′
  complete^SNe v <>                  refl c[v]^sn   = var v
  complete^SNe v (app c t^SN)        refl c[v]∙t^sn =
    app (complete^SNe v c refl (`∙t⁻¹^sn c[v]∙t^sn)) t^SN
  complete^SNe v (cas c l^SN r^SN)   refl c[v]lr^sn =
    cas (complete^SNe v c refl (`case₁⁻¹^sn c[v]lr^sn)) l^SN r^SN
  complete^SNe v (rec ze^SN su^SN c) refl czs[v]^sn =
    rec ze^SN su^SN (complete^SNe v c refl (`rec₃⁻¹^sn czs[v]^sn))

  -- 2.
  complete^SN-βι : ∀ {Γ α σ i} (r : Γ ⊢↯ α) c →
    let t = cut (unRed r) c in Γ ⊢ σ ∋ t ↝SN cut (βιRed r) c →
    ∀ {t′} → t′ ≡ t → Γ ⊢sn σ ∋ t′ < i → Γ ⊢SN σ ∋ t′
  complete^SN-βι t c r refl (sn p) = red r (complete^SN _ (p (cut^↝ c (fire t))))

  -- 3.
  complete^SN : ∀ {Γ σ i} t → Γ ⊢sn σ ∋ t < i → Γ ⊢SN σ ∋ t
  complete^SN (`var v)      v^sn  = neu (var v)
  complete^SN (`i₁ t)       it^sn = inl (complete^SN t (`i₁⁻¹^sn it^sn))
  complete^SN (`i₂ t)       it^sn = inr (complete^SN t (`i₂⁻¹^sn it^sn))
  complete^SN `0            ze^sn = zro
  complete^SN (`1+ t)       st^sn = suc (complete^SN t (`1+⁻¹^sn st^sn))
  complete^SN (`λ b)        λb^sn = lam (complete^SN b (`λ⁻¹^sn λb^sn))
  complete^SN (f `∙ t)      ft^sn =
    let (f^sn , t^sn) = `∙⁻¹^sn ft^sn in
    let t^SN = complete^SN t t^sn in
    elim^SN f (app t) f^sn (app <> t^SN) ft^sn
  complete^SN (`case t l r) tlr^sn =
    let (t^sn , l^sn , r^sn) = `case⁻¹^sn tlr^sn in
    let (l^SN , r^SN) = (complete^SN l l^sn , complete^SN r r^sn) in
    elim^SN t (cas l r) t^sn (cas <> l^SN r^SN) tlr^sn
  complete^SN (`rec ze su t) zst^sn =
    let (ze^sn , su^sn , t^sn) = `rec⁻¹^sn zst^sn in
    let (ze^SN , su^SN) = (complete^SN ze ze^sn , complete^SN su su^sn) in
    elim^SN t (rec ze su) t^sn (rec ze^SN su^SN <>) zst^sn

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
  -- redex
  spine^SN (`var v) e tm^sn e^SN = _ , elim e , inj₁ (v , refl , e^SN)
  spine^SN (`λ b) (app t) tm^sn (app <> t^SN) = _ , <> , inj₂ (β b t , refl , β b t t^SN)
  spine^SN (`i₁ t) (cas l r) tm^sn (cas <> l^SN r^SN) =
    let t^SN = complete^SN t (`i₁⁻¹^sn tm^sn) in
    _ , <> , inj₂ (ι₁ t l r , refl , ι₁ t l r t^SN r^SN)
  spine^SN (`i₂ t) (cas l r) tm^sn (cas <> l^SN r^SN) =
    let t^SN = complete^SN t (`i₂⁻¹^sn tm^sn) in
    _ , <> , inj₂ (ι₂ t l r , refl , ι₂ t l r t^SN l^SN)
  spine^SN `0 (rec ze su) tm^sn (rec ze^SN su^SN <>) =
    _ , <> , inj₂ (ιz ze su , refl , ιz ze su su^SN)
  spine^SN (`1+ t) (rec ze su) tm^sn (rec ze^SN su^SN <>) =
    let t^SN = complete^SN t (`1+⁻¹^sn tm^sn) in
    _ , <> , inj₂ (ιs ze su t , refl , ιs ze su t ze^SN t^SN)
  -- structural (TODO: refactor?)
  spine^SN (f `∙ t) e tm^sn e^SN =
    let (f^sn , t^sn) = `∙⁻¹^sn tm^sn in
    let t^SN = complete^SN t t^sn in
    case spine^SN f (app t) f^sn (app <> t^SN) of λ where
      (_ , c , inj₁ (v , eq , c^SN)) →
        _ , (elim e ∘C c) , inj₁ (v , spine-eq e c eq , ∘C^R e^SN c^SN)
      (_ , c , inj₂ (r , eq , r^SN)) →
        _ , (elim e ∘C c) , inj₂ (r , spine-eq e c eq , spine-red e c r r^SN)
  spine^SN (`case t l r) e tm^sn e^SN =
    let (t^sn , l^sn , r^sn) = `case⁻¹^sn tm^sn in
    let (l^SN , r^SN) = (complete^SN l l^sn , complete^SN r r^sn) in
    case spine^SN t (cas l r) t^sn (cas <> l^SN r^SN) of λ where
      (_ , c , inj₁ (v , eq , c^SN)) →
        _ , (elim e ∘C c) , inj₁ (v , spine-eq e c eq , ∘C^R e^SN c^SN)
      (_ , c , inj₂ (r , eq , r^SN)) →
        _ , (elim e ∘C c) , inj₂ (r , spine-eq e c eq , spine-red e c r r^SN)
  spine^SN (`rec ze su t) e tm^sn e^SN =
    let (ze^sn , su^sn , t^sn) = `rec⁻¹^sn tm^sn in
    let (ze^SN , su^SN) = (complete^SN ze ze^sn , complete^SN su su^sn) in
    case spine^SN t (rec ze su) t^sn (rec ze^SN su^SN <>) of λ where
      (_ , c , inj₁ (v , eq , c^SN)) →
        _ , (elim e ∘C c) , inj₁ (v , spine-eq e c eq , ∘C^R e^SN c^SN)
      (_ , c , inj₂ (r , eq , r^SN)) →
        _ , (elim e ∘C c) , inj₂ (r , spine-eq e c eq , spine-red e c r r^SN)

  spine-eq : ∀ {Γ α β σ t tc} (e : Elim Γ σ β) (c : Γ ∣ α ⊢ β) →
             tc ≡ cut t c → cut tc (elim e) ≡ cut t (elim e ∘C c)
  spine-eq e c refl = cut-∘C _ (elim e) c

  spine-red : ∀ {Γ α β σ} e c → (r : Γ ⊢↯ α) →
              Γ ⊢ β ∋ cut (unRed r) c ↝SN cut (βιRed r) c →
              Γ ⊢ σ ∋ cut (unRed r) (elim e ∘C c) ↝SN cut (βιRed r) (elim e ∘C c)
  spine-red (app t)   c r r^SN = [∙]₂ r^SN t
  spine-red (cas _ _) c r r^SN = [c]₁ r^SN _ _
  spine-red (rec _ _) c r r^SN = [r]₃ _ _ r^SN

-- Section 5 Reducibility Candidates
-------------------------------------------------------------------

infix 2 <_>
data <_> {Γ σ} (𝓢 : Term σ Γ → Set) (t : Term σ Γ) : Set where
  cnd : 𝓢 t → < 𝓢 > t
  neu : Γ ⊢SNe σ ∋ t → < 𝓢 > t
  red : ∀ {t′} → Γ ⊢ σ ∋ t ↝SN t′ → < 𝓢 > t′ → < 𝓢 > t

infix 3 _+𝓡_
data _+𝓡_ {Γ σ τ} (𝓢 : Term σ Γ → Set) (𝓣 : Term τ Γ → Set) : Term (σ + τ) Γ → Set where
  inl : ∀ {t} → 𝓢 t → (𝓢 +𝓡 𝓣) (`i₁ t)
  inr : ∀ {t} → 𝓣 t → (𝓢 +𝓡 𝓣) (`i₂ t)

data ℕ𝓡 {Γ} : Size → Term ℕ Γ → Set where
  zro : ∀ {i} → ℕ𝓡 (↑ i) `0
  suc : ∀ {i t} → < ℕ𝓡 i > t → ℕ𝓡 (↑ i) (`1+ t)

infix 3 _⊢𝓡_∋_
_⊢𝓡_∋_     : ∀ Γ σ → Term σ Γ → Set
Γ ⊢𝓡 α     ∋ t = Γ ⊢SN α ∋ t
Γ ⊢𝓡 ℕ     ∋ t = < ℕ𝓡 _ > t
Γ ⊢𝓡 σ + τ ∋ t = < (Γ ⊢𝓡 σ ∋_) +𝓡 (Γ ⊢𝓡 τ ∋_) > t
Γ ⊢𝓡 σ ⇒ τ ∋ t = ∀ {Δ} ρ {u} → Δ ⊢𝓡 σ ∋ u → Δ ⊢𝓡 τ ∋ ren ρ t `∙ u

𝓡^P : Pred Term
pred 𝓡^P = _ ⊢𝓡 _ ∋_

Quote : List Type → Type → Set
Quote Γ σ = ∀ {t} → Γ ⊢𝓡 σ ∋ t → Γ ⊢SN σ ∋ t

-- Theorem 5.1
quote^<>  : ∀ {Γ σ 𝓢} → (∀ {t} → 𝓢 t → Γ ⊢SN σ ∋ t) →
            ∀ {t} → < 𝓢 > t → Γ ⊢SN σ ∋ t
quote^<> σ^𝓡 (cnd t^𝓡)   = σ^𝓡 t^𝓡
quote^<> σ^𝓡 (neu t^SNe)  = neu t^SNe
quote^<> σ^𝓡 (red r t^𝓡) = red r (quote^<> σ^𝓡 t^𝓡)

quote^+𝓡  : ∀ {Γ σ τ} → Quote Γ σ → Quote Γ τ →
             ∀ {t} → ((Γ ⊢𝓡 σ ∋_) +𝓡 (Γ ⊢𝓡 τ ∋_)) t → Γ ⊢SN σ + τ ∋ t
quote^+𝓡 σ^𝓡 τ^𝓡 (inl t^𝓡) = inl (σ^𝓡 t^𝓡)
quote^+𝓡 σ^𝓡 τ^𝓡 (inr t^𝓡) = inr (τ^𝓡 t^𝓡)

quote^ℕ𝓡 : ∀ {Γ t i} → ℕ𝓡 i t → Γ ⊢SN ℕ ∋ t
quote^ℕ𝓡 zro        = zro
quote^ℕ𝓡 (suc t^𝓡) = suc (quote^<> quote^ℕ𝓡 t^𝓡)

mutual

 -- 1.
 quote^𝓡 : ∀ {Γ} σ → Quote Γ σ
 quote^𝓡 α       t^𝓡         = t^𝓡
 quote^𝓡 ℕ       t^𝓡         = quote^<> quote^ℕ𝓡 t^𝓡
 quote^𝓡 (σ + τ) t^𝓡         = quote^<> (quote^+𝓡 (quote^𝓡 σ) (quote^𝓡 τ)) t^𝓡
 quote^𝓡 (σ ⇒ τ) t^𝓡         = th⁻¹^SN _ embed refl (SN-ext z tz^SN)
   where z^𝓡  = unquote^𝓡 σ (var z)
         embed = pack s
         tz^SN = quote^𝓡 τ (t^𝓡 embed z^𝓡)

 -- 2.
 unquote^𝓡 : ∀ {Γ} σ {t} → Γ ⊢SNe σ ∋ t → Γ ⊢𝓡 σ ∋ t
 unquote^𝓡 α       t^SNe        = neu t^SNe
 unquote^𝓡 ℕ       t^SNe        = neu t^SNe
 unquote^𝓡 (σ + τ) t^SNe        = neu t^SNe
 unquote^𝓡 (σ ⇒ τ) t^SNe ρ u^𝓡 = unquote^𝓡 τ (app (th^SNe ρ t^SNe) u^SN)
   where u^SN = quote^𝓡 σ u^𝓡

-- 3.
↝SN⁻¹^𝓡 : ∀ {Γ} σ {t′ t} → Γ ⊢ σ ∋ t′ ↝SN t → Γ ⊢𝓡 σ ∋ t → Γ ⊢𝓡 σ ∋ t′
↝SN⁻¹^𝓡 α       r t^𝓡 = red r t^𝓡
↝SN⁻¹^𝓡 ℕ       r t^𝓡 = red r t^𝓡
↝SN⁻¹^𝓡 (σ + τ) r t^𝓡 = red r t^𝓡
↝SN⁻¹^𝓡 (σ ⇒ τ) r t^𝓡 = λ ρ u^𝓡 → ↝SN⁻¹^𝓡 τ ([∙]₂ (th^↝SN ρ r) _) (t^𝓡 ρ u^𝓡)

th^<> : ∀ {σ} {𝓢 : ∀ {Γ} → Term σ Γ → Set}
        (th^𝓢 : ∀ {Γ Δ t} (ρ : Thinning Γ Δ) → 𝓢 t → 𝓢 (ren ρ t)) →
        ∀ {Γ Δ t} (ρ : Thinning Γ Δ) → < 𝓢 > t → < 𝓢 > (ren ρ t)
th^<> th^𝓢 ρ (cnd t^𝓢)   = cnd (th^𝓢 ρ t^𝓢)
th^<> th^𝓢 ρ (neu t^SNe)  = neu (th^SNe ρ t^SNe)
th^<> th^𝓢 ρ (red r t^𝓢) = red (th^↝SN ρ r) (th^<> th^𝓢 ρ t^𝓢)

th^ℕ𝓡 : ∀ {i Γ Δ t} (ρ : Thinning Γ Δ) → ℕ𝓡 i t → ℕ𝓡 i (ren ρ t)
th^ℕ𝓡 ρ zro            = zro
th^ℕ𝓡 ρ (suc {i} t^𝓡) = suc (th^<> (th^ℕ𝓡 {i}) ρ t^𝓡)

th^+𝓡 : ∀ {σ τ} {𝓢 : ∀ {Γ} → Term σ Γ → Set} {𝓣 : ∀ {Γ} → Term τ Γ → Set}
         (th^𝓢 : ∀ {Γ Δ} (ρ : Thinning Γ Δ) → ∀ t → 𝓢 t → 𝓢 (ren ρ t)) →
         (th^𝓣 : ∀ {Γ Δ} (ρ : Thinning Γ Δ) → ∀ t → 𝓣 t → 𝓣 (ren ρ t)) →
         ∀ {Γ Δ t} (ρ : Thinning Γ Δ) → (𝓢 +𝓡 𝓣) t → (𝓢 +𝓡 𝓣) (ren ρ t)
th^+𝓡 th^𝓢 th^𝓣 ρ (inl t^𝓢) = inl (th^𝓢 ρ _ t^𝓢)
th^+𝓡 th^𝓢 th^𝓣 ρ (inr t^𝓣) = inr (th^𝓣 ρ _ t^𝓣)

th^𝓡 : (σ : Type) → ∀ {Γ Δ} ρ t → Γ ⊢𝓡 σ ∋ t → Δ ⊢𝓡 σ ∋ ren ρ t
th^𝓡 α       ρ t t^𝓡         = th^SN ρ t^𝓡
th^𝓡 ℕ       ρ t t^𝓡         = th^<> th^ℕ𝓡 ρ t^𝓡
th^𝓡 (σ + τ) ρ t t^𝓡         = th^<> (th^+𝓡 (th^𝓡 σ) (th^𝓡 τ)) ρ t^𝓡
th^𝓡 (σ ⇒ τ) ρ t t^𝓡 ρ′ u^𝓡 = cast (t^𝓡 (select ρ ρ′) u^𝓡)
  where cast = subst (λ t → _ ⊢𝓡 _ ∋ t `∙ _) (sym $ ren² TermD t ρ ρ′)

app^𝓡 : ∀ {σ τ Γ} f t → Γ ⊢𝓡 σ ⇒ τ ∋ f → Γ ⊢𝓡 σ ∋ t → Γ ⊢𝓡 τ ∋ f `∙ t
app^𝓡 f t f^𝓡 t^𝓡 = cast (f^𝓡 (base vl^Var) t^𝓡)
  where cast = subst (λ f → _ ⊢𝓡 _ ∋ f `∙ t) (ren-id f)

reify^𝓡 : ∀ Θ τ {Γ Δ i} (sc : Scope (Tm TermD i) Θ τ Γ) (ρ : (Γ ─Env) Term Δ) →
  Kripke^P 𝓡^P 𝓡^P Θ τ (Sem.body Substitution ρ Θ τ sc) →
  (Θ ++ Δ) ⊢SN τ ∋ sub (lift vl^Tm Θ ρ) sc
reify^𝓡 []        τ sc ρ sc^P = cast (quote^𝓡 _ sc^P) where

  cast = subst (_ ⊢SN _ ∋_) (Sim.sim Sim.SubExt (lift[]^Tm ρ) sc)
reify^𝓡 Θ@(_ ∷ _) τ sc ρ sc^P = quote^𝓡 τ (sc^P nms (nms^R)) where

  nms = freshʳ vl^Var Θ

  nms^R : pred.∀[ 𝓡^P ] (freshˡ vl^Tm _)
  lookup^P nms^R k = unquote^𝓡 _ (lookup^P freshˡ^SNe k)


sub^𝓡 : ∀ Θ τ {i Γ Δ} (sc : Scope (Tm TermD i) Θ τ Γ) (vs : (Θ ─Env) Term Δ) (ρ : (Γ ─Env) Term Δ) →
         Kripke^P 𝓡^P 𝓡^P Θ τ (Sem.body Substitution ρ Θ τ sc) →
         pred.∀[ 𝓡^P ] vs →
         Δ ⊢𝓡 τ ∋ sub (vs >> base vl^Tm) (sub (lift vl^Tm Θ ρ) sc)
sub^𝓡 [] τ sc vs ρ sc^R vs^R = cast sc^R where

  sub^R : rel.∀[ Eq^R ] (sub (vs >> base vl^Tm) <$> lift vl^Tm [] ρ) ρ
  lookup^R sub^R k = begin
    sub (vs >> base vl^Tm) (ren (th^Env th^Var (base vl^Var) (pack id)) (lookup ρ k))
      ≡⟨ rensub TermD (lookup ρ k) (th^Env th^Var (base vl^Var) (pack id)) (vs >> base vl^Tm) ⟩
    sub (select (th^Env th^Var (base vl^Var) (pack id)) (base vl^Tm)) (lookup ρ k)
      ≡⟨ Sim.sim Sim.SubExt (pack^R (λ v → cong (lookup (base vl^Tm)) (lookup-base^Var v))) (lookup ρ k) ⟩
    sub (base vl^Tm) (lookup ρ k)
      ≡⟨ sub-id (lookup ρ k) ⟩
    lookup ρ k
      ∎

  cast = subst (_ ⊢𝓡 τ ∋_) (sym (Fus.fus (Sub² TermD) sub^R sc))
sub^𝓡 Θ@(_ ∷ _) τ sc vs ρ sc^R vs^R = cast (sc^R (base vl^Var) vs^R) where

  sub^R : rel.∀[ Eq^R ] (sub (vs >> base vl^Tm) <$> lift vl^Tm Θ ρ)
                        (vs >> th^Env th^Tm ρ (base vl^Var))
  lookup^R sub^R k with split Θ k
  ... | inj₁ k₁ = begin
    sub (vs >> base vl^Tm) (ren (pack (injectˡ _)) (lookup ((th^Env th^Tm (base vl^Tm) (pack s)) ∙ `var z) k₁))
      ≡⟨ cong (λ v → sub (vs >> base vl^Tm) (ren (pack (injectˡ _)) v)) (lookup^R th^base^s∙z k₁) ⟩
     sub (vs >> base vl^Tm) (ren (pack (injectˡ _)) (`var k₁))
       ≡⟨ injectˡ->> vs (base vl^Tm) k₁ ⟩
    lookup vs k₁
      ∎
  ... | inj₂ k₂ = begin
    sub (vs >> base vl^Tm) (ren (th^Env th^Var (base vl^Var) (pack (injectʳ Θ))) (lookup ρ k₂))
      ≡⟨ rensub TermD (lookup ρ k₂) (th^Env th^Var (base vl^Var) (pack (injectʳ Θ))) (vs >> base vl^Tm) ⟩
    sub (select (th^Env th^Var (base vl^Var) (pack (injectʳ Θ))) (vs >> base vl^Tm)) (lookup ρ k₂)
      ≡⟨ Sim.sim Sim.SubExt sub'^R (lookup ρ k₂) ⟩
    sub (`var <$> base vl^Var) (lookup ρ k₂)
      ≡⟨ sym (Sim.rensub (base vl^Var) (lookup ρ k₂)) ⟩
    ren (base vl^Var) (lookup ρ k₂)
      ∎ where

     sub'^R : rel.∀[ Eq^R ] (select (th^Env th^Var (base vl^Var) (pack (injectʳ Θ))) (vs >> base vl^Tm))
                            (`var <$> base vl^Var)
     lookup^R sub'^R k = begin
       lookup (vs >> base vl^Tm) (lookup {𝓥 = Var} (pack (injectʳ Θ)) (lookup (base vl^Var) k))
         ≡⟨ cong (λ v → lookup (vs >> base vl^Tm) (lookup {𝓥 = Var} (pack (injectʳ Θ)) v)) (lookup-base^Var k) ⟩
       lookup (vs >> base vl^Tm) (injectʳ Θ k)
         ≡⟨ injectʳ->> vs (base vl^Tm) k ⟩
       lookup (base vl^Tm) k
         ≡⟨ sym (lookup^R base^VarTm^R k) ⟩
       lookup {𝓥 = Term} (`var <$> base vl^Var) k
         ∎

  cast = subst (_ ⊢𝓡 τ ∋_) (sym (Fus.fus (Sub² TermD) sub^R sc))

[/0]^𝓡 :
  ∀ σ τ {Γ Δ i} t (l : Tm TermD i τ (σ ∷ Γ)) (ρ : (Γ ─Env) Term Δ) →
  Δ ⊢𝓡 σ ∋ t →
  Kripke^P 𝓡^P 𝓡^P (σ ∷ []) τ (Sem.body Substitution ρ (σ ∷ []) τ l) →
  Δ ⊢𝓡 τ ∋ sub (lift vl^Tm (σ ∷ []) ρ) l [ t /0]
[/0]^𝓡 σ τ t l ρ t^P l^P = cast (sub^𝓡 (σ ∷ []) τ l (ε ∙ t) ρ l^P (ε^P ∙^P t^P)) where

  sub^R : rel.∀[ Eq^R ] ((ε ∙ t) >> base vl^Tm) (t /0])
  lookup^R sub^R z     = refl
  lookup^R sub^R (s v) = refl

  cast = subst (_ ⊢𝓡 τ ∋_) (Sim.sim Sim.SubExt sub^R (sub _ l))


case^𝓡 : ∀ {σ τ ν i Γ Δ} (t : Term (σ + τ) Δ)
  (l : Tm TermD i ν (σ ∷ Γ)) (r : Tm TermD i ν (τ ∷ Γ))
  (ρ : (Γ ─Env) Term Δ) → Δ ⊢𝓡 σ + τ ∋ t →
  Kripke^P 𝓡^P 𝓡^P (σ ∷ []) ν (Sem.body Substitution ρ (σ ∷ []) ν l) →
  Kripke^P 𝓡^P 𝓡^P (τ ∷ []) ν (Sem.body Substitution ρ (τ ∷ []) ν r) →
  Δ ⊢𝓡 ν ∋ `case t (sub (lift vl^Tm (σ ∷ []) ρ) l) (sub (lift vl^Tm (τ ∷ []) ρ) r)
case^𝓡 {σ} {τ} {ν} t bl br ρ (neu t^SNe) bl^P br^P =
  unquote^𝓡 ν (cas t^SNe (reify^𝓡 (σ ∷ []) ν bl ρ bl^P) (reify^𝓡 (τ ∷ []) ν br ρ br^P))
case^𝓡 t        bl br ρ (red r t^P) bl^P br^P =
  ↝SN⁻¹^𝓡 _ ([c]₁ r (sub _ bl) (sub _ br)) (case^𝓡 _ bl br ρ t^P bl^P br^P)
case^𝓡 {σ} {τ} {ν} (`i₁ t) bl br ρ (cnd (inl t^P))   bl^P br^P =
  ↝SN⁻¹^𝓡 _ (ι₁ t (sub _ bl) (sub _ br) (quote^𝓡 _ t^P) (reify^𝓡 (τ ∷ []) ν br ρ br^P))
             ([/0]^𝓡 _ _ t bl ρ t^P bl^P)
case^𝓡 {σ} {τ} {ν} (`i₂ t) bl br ρ (cnd (inr t^P))   bl^P br^P =
  ↝SN⁻¹^𝓡 _ (ι₂ t (sub _ bl) (sub _ br) (quote^𝓡 _ t^P) (reify^𝓡 (σ ∷ []) ν bl ρ bl^P))
             ([/0]^𝓡 _ _ t br ρ t^P br^P)

rec^𝓡 : ∀ {σ i Γ Δ} (ze : Tm TermD i σ Γ) (su : Tm TermD i σ (σ ∷ ℕ ∷ Γ))
  (t : Term ℕ Δ) (ρ : (Γ ─Env) Term Δ) →
  Δ ⊢𝓡 σ ∋ sub ρ ze → Kripke^P 𝓡^P 𝓡^P (σ ∷ ℕ ∷ []) σ (Sem.body Substitution ρ (σ ∷ ℕ ∷ []) σ su) →
  Δ ⊢𝓡 ℕ ∋ t →
  Δ ⊢𝓡 σ ∋ `rec (sub ρ ze) (sub (lift vl^Tm (σ ∷ ℕ ∷ []) ρ) su) t
-- stuck / ↝SN
rec^𝓡 {σ} ze su t ρ ze^𝓡 su^𝓡 (neu t^SNe) =
  unquote^𝓡 σ (rec (quote^𝓡 _ ze^𝓡) (reify^𝓡 (σ ∷ ℕ ∷ []) σ su ρ su^𝓡) t^SNe)
rec^𝓡 {σ} ze su t ρ ze^𝓡 su^𝓡 (red r t^𝓡) =
  ↝SN⁻¹^𝓡 σ ([r]₃ (sub ρ ze) (sub _ su) r) (rec^𝓡 ze su _ ρ ze^𝓡 su^𝓡 t^𝓡)
-- ι-redex
rec^𝓡 ze su .`0 ρ ze^𝓡 su^𝓡 (cnd zro)        =
  ↝SN⁻¹^𝓡 _ (ιz (sub ρ ze) (sub _ su) (reify^𝓡 (_ ∷ ℕ ∷ []) _ su ρ su^𝓡)) ze^𝓡
rec^𝓡 {σ} ze su .(`1+ _) ρ ze^𝓡 su^𝓡 (cnd (suc {t = t} t^𝓡)) =
  ↝SN⁻¹^𝓡 _ (ιs (sub ρ ze) (sub _ su) _ (quote^𝓡 σ ze^𝓡) (quote^𝓡 ℕ t^𝓡))
  $ subst (_ ⊢𝓡 σ ∋_) (Sim.sim Sim.SubExt sub^R (sub (lift vl^Tm (σ ∷ ℕ ∷ []) ρ) su))
  $ sub^𝓡 (σ ∷ ℕ ∷ []) σ su (ε ∙ t ∙ `rec (sub ρ ze) (sub _  su) t) ρ su^𝓡
    (ε^P ∙^P t^𝓡 ∙^P rec^𝓡 ze su t ρ ze^𝓡 su^𝓡 t^𝓡) where

   sub^R : rel.∀[ Eq^R ] ((ε ∙ t ∙ `rec (sub ρ ze) (sub _ su) t) >> base vl^Tm)
                         (base vl^Tm ∙ t ∙ `rec (sub ρ ze) (sub _ su) t)
   lookup^R sub^R z          = refl
   lookup^R sub^R (s z)      = refl
   lookup^R sub^R (s (s v))  = refl

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
  -- constructors
  alg^P (`i₁' t) ρ^P (t^P , _)  = cnd (inl t^P)
  alg^P (`i₂' t) ρ^P (t^P , _)  = cnd (inr t^P)
  alg^P `0'      ρ^P _          = cnd zro
  alg^P (`1+' t) ρ^P (t^P , _)  = cnd (suc t^P)
  -- eliminators
  alg^P (`case' t l r)  {ρ} ρ^P (t^P , l^P , r^P , _) = case^𝓡 (sub ρ t) l r ρ t^P l^P r^P
  alg^P (`rec' ze su t)     ρ^P (z^P , s^P , t^P , _) = rec^𝓡 ze su (sub _ t) _ z^P s^P t^P
  alg^P (f `∙' t)           ρ^P (f^P , t^P , _)       = app^𝓡 (sub _ f) (sub _ t) f^P t^P
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
        sub _ (lookup ρ₁ k)                           ≡⟨ sym $ Sim.sim Sim.RenSub ρ^R (lookup ρ₁ k) ⟩
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

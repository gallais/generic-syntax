\begin{code}
module Generic.Examples.POPLMark2 where

open import var hiding (_<$>_)
open import rel
open import varlike
open import indexed
open import environment
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Unit
open import Generic.Zip
open import Generic.Simulation as Sim hiding (rensub ; RenSub)
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
pattern `λ  b    = `con ((_ , _) , true , b , refl)
pattern _`∙_ f t = `con ((_ , _) , false , f , t , refl)

{-# DISPLAY `con (_ , true , b , refl)      = `λ b   #-}
{-# DISPLAY `con (_ , false , f , t , refl) = f `∙ t #-}

Term : Type ─Scoped
Term = Tm TermD ∞

infix 3 _↝_
data _↝_ : ∀ {σ} → [ Term σ ⟶ Term σ ⟶ κ Set ] where
-- computational
  β    : ∀ {Γ σ τ} (t : Term τ (σ ∷ Γ)) (u : Term σ Γ) → `λ t `∙ u ↝ t [ u /0]
-- structural
  [λ]  : ∀ {Γ σ τ} {t u : Term τ (σ ∷ Γ)} → t ↝ u → `λ t ↝ `λ u
  [∙]₁ : ∀ {Γ σ τ} (f : Term (σ ⇒ τ) Γ) {t u : Term σ Γ} → t ↝ u → f `∙ t ↝ f `∙ u
  [∙]₂ : ∀ {Γ σ τ} {f g : Term (σ ⇒ τ) Γ} → f ↝ g → (t : Term σ Γ) → f `∙ t ↝ g `∙ t

th^↝ : ∀ {σ Γ Δ} {t u : Term σ Γ} (ρ : Thinning Γ Δ) → t ↝ u → ren ρ t ↝ ren ρ u
th^↝ ρ (β t u)    = subst (ren ρ (`λ t `∙ u) ↝_) (sym $ renβ TermD t u ρ) (β _ _)
th^↝ ρ ([λ] r)    = [λ] (th^↝ _ r)
th^↝ ρ ([∙]₁ f r) = [∙]₁ (ren ρ f) (th^↝ ρ r)
th^↝ ρ ([∙]₂ r t) = [∙]₂ (th^↝ ρ r) (ren ρ t)

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

data SN {σ Γ} (t : Term σ Γ) : Set where
  sn : (∀ {u} → t ↝ u → SN u) → SN t

Red : Rel Term Unit -- predicate = binary relation with boring second component
𝓡 : ∀ {σ} → [ Term σ ⟶ κ Set ]

rel Red {α}         t _ = SN t
rel Red {σ ⇒ τ} {Γ} t _ = ∀ {Δ} (ρ : Thinning Γ Δ) {u} → 𝓡 u → 𝓡 (ren ρ t `∙ u)

𝓡 t = rel Red t _

SN-`λ : ∀ {σ τ} {Γ} {t : Term τ (σ ∷ Γ)} → SN t → SN (`λ t)
SN-`λ (sn t^R) = sn λ { ([λ] r) → SN-`λ (t^R r) }

-- TODO: generic proof!
ren-id' : ∀ {σ Γ} {ρ : Thinning Γ Γ} → ∀[ Eq^R ] ρ (base vl^Var) →
          (t : Term σ Γ) → ren ρ t ≡ t
ren-id' ρ^R (`var k) = cong `var (trans (lookup^R ρ^R k) (lookup-base^Var k))
ren-id' ρ^R (f `∙ t) = cong₂ _`∙_ (ren-id' ρ^R f) (ren-id' ρ^R t)
ren-id' ρ^R (`λ b)   = cong `λ $ ren-id' ρ^R′ b where

  ρ^R′ : ∀[ Eq^R ] _ (base vl^Var)
  lookup^R ρ^R′ z     = refl
  lookup^R ρ^R′ (s k) = cong s (trans (lookup-base^Var _) (lookup^R ρ^R k))

ren-id : ∀ {σ Γ} (t : Term σ Γ) → ren (base vl^Var) t ≡ t
ren-id = ren-id' (pack^R λ _ → refl)

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

data NE : ∀ {σ Γ} → Term σ Γ → Set where
  `var : ∀ {σ Γ} (k : Var σ Γ) → NE (`var k)
  _`$_ : ∀ {σ τ Γ} {f : Term (σ ⇒ τ) Γ} → NE f → (t : Term σ Γ) → NE (f `∙ t)

NE-↝ : ∀ {σ Γ} {t u : Term σ Γ} → t ↝ u → NE t → NE u
NE-↝ (β _ _)    (() `$ _)
NE-↝ ([λ] r)    ()
NE-↝ ([∙]₁ f r) (ne `$ _) = ne `$ _
NE-↝ ([∙]₂ r t) (ne `$ _) = NE-↝ r ne `$ t

th^NE : ∀ {σ Γ Δ} {t : Term σ Γ} (ρ : Thinning Γ Δ) → NE t → NE (ren ρ t)
th^NE ρ (`var k)  = `var (lookup ρ k)
th^NE ρ (ne `$ t) = th^NE ρ ne `$ ren ρ t

SN-`∙ : ∀ {σ τ Γ} {t : Term (σ ⇒ τ) Γ} → NE t → SN t → {u : Term σ Γ} → SN u → SN (t `∙ u)
SN-`∙ t^NE t^SN u^SN = sn (aux t^NE t^SN u^SN) where

  aux : ∀ {σ τ Γ} {t : Term (σ ⇒ τ) Γ} {u : Term σ Γ} → NE t → SN t → SN u → ∀ {v} → t `∙ u ↝ v → SN v
  aux ()   t^SN      u^SN      (β _ _)
  aux t^NE t^SN      (sn u^SN) ([∙]₁ f r) = sn (aux t^NE t^SN (u^SN r))
  aux t^NE (sn t^SN) u^SN      ([∙]₂ r t) = sn (aux (NE-↝ r t^NE) (t^SN r) u^SN)

𝓡⇒SN : ∀ σ {Γ} (t : Term σ Γ) → 𝓡 t → SN t
NE⇒𝓡 : ∀ σ {Γ} (t : Term σ Γ) → NE t → SN t → 𝓡 t

𝓡⇒SN α       t t^R = t^R
𝓡⇒SN (σ ⇒ τ) t t^R = SN-η ηt where

  𝓡[t∙z] : 𝓡 (ren extend t `∙ `var z)
  𝓡[t∙z] = lemma2-1 (lemma2-3 (σ ⇒ τ) extend t t^R) (NE⇒𝓡 σ (`var z) (`var z) (sn λ ()))

  ηt : SN (`λ (ren extend t `∙ `var z))
  ηt = SN-`λ (𝓡⇒SN τ (ren extend t `∙ `var z) 𝓡[t∙z])

NE⇒𝓡 α       t t^NE t^SN = t^SN
NE⇒𝓡 (σ ⇒ τ) t t^NE t^SN = λ ρ {u} u^SN →
  let tρ^NE = th^NE ρ t^NE
      tρ^SN = lemma2-2 ρ t^SN
  in NE⇒𝓡 τ _ (tρ^NE `$ u) (SN-`∙ tρ^NE tρ^SN (𝓡⇒SN σ u u^SN))

lemma2-4 : ∀ {Γ Δ Θ} (ρ : Thinning Δ Θ) (vs : (Γ ─Env) Term Δ) →
           ∀[ Red ] vs _ → ∀[ Red ] (th^Env th^Tm vs ρ) _
lemma2-4 ρ vs rs = lemma2-3 _ ρ _ <$>^R rs

lemma2-5 : ∀ τ {σ Γ} {t : Term τ (σ ∷ Γ)} {u : Term σ Γ} → SN u → 𝓡 (t [ u /0]) → 𝓡 (`λ t `∙ u)
lemma2-5 = {!!}

theorem2-6 : ∀ {σ Γ Δ} (t : Term σ Γ) (ρ : (Γ ─Env) Term Δ) →
             ∀[ Red ] ρ _ → 𝓡 (sub ρ t)
theorem2-6 t ρ rs = Sim.sim prf rs t where

  prf : Sim Red Red TermD Substitution _
  Sim.th^R  prf = λ ρ → lemma2-3 _ ρ _
  Sim.var^R prf = id
  Sim.alg^R prf = alg^R where

    alg^R : ∀ {Γ Δ σ s} (b : ⟦ TermD ⟧ (Scope (Tm TermD s)) σ Γ) {ρ₁ : (Γ ─Env) Term Δ} {ρ₂} → ∀[ Red ] ρ₁ ρ₂ →
            let v₁ = fmap TermD (Sem.body Substitution ρ₁) b
                v₂ = fmap TermD (Sem.body SemUnit ρ₂) b
            in Zip TermD (Kripke^R Red Red) v₁ v₂  → 𝓡 (Sem.alg Substitution v₁)
    alg^R ((σ , τ) , false , f , t , refl) {ρ₁} ρ^R (refl , refl , f^R , t^R , _) =
      subst (λ f → 𝓡 (f `∙ sub ρ₁ t)) (ren-id _) (f^R (base vl^Var) t^R)

    alg^R t@((σ , τ) , true , b , refl)      {ρ₁} _ (refl , refl , b^R , _) ρ {u} u^R =
       𝓡 (ren ρ (sub ρ₁ (`λ b)) `∙ u) ∋ lemma2-5 τ (𝓡⇒SN σ u u^R)
      (𝓡 (ren ρ′ (sub ρ₁′ b) [ u /0]) ∋ subst 𝓡 eq bu) where

        bu : 𝓡 (sub ((ε ∙ u) >> th^Env th^Tm ρ₁ ρ) b)
        bu = b^R ρ (ε^R ∙^R u^R)

        ρ′  = lift vl^Var (σ ∷ []) ρ
        ρ₁′ = lift vl^Tm (σ ∷ []) ρ₁

        ρ^R : ∀[ VarTm^R ] ρ (select (freshʳ vl^Var (σ ∷ [])) (select ρ′ (u /0])))
        lookup^R ρ^R k = sym $ begin
          lookup (base vl^Tm) (lookup (base vl^Var) (lookup ρ (lookup (base vl^Var) k)))
            ≡⟨ lookup-base^Tm _ ⟩
          `var (lookup (base vl^Var) (lookup ρ (lookup (base vl^Var) k)))
            ≡⟨ cong `var (lookup-base^Var _) ⟩
          `var (lookup ρ (lookup (base vl^Var) k))
            ≡⟨ cong (`var ∘ lookup ρ) (lookup-base^Var k) ⟩
          `var (lookup ρ k) ∎

        ρ^R′ : ∀[ Eq^R ] (sub (select ρ′ (u /0])) <$> ρ₁′) ((ε ∙ u) >> th^Env th^Tm ρ₁ ρ)
        lookup^R ρ^R′ z     = refl
        lookup^R ρ^R′ (s k) = begin
          sub (select ρ′ (u /0])) (lookup ρ₁′ (s k))    ≡⟨⟩
          sub (select ρ′ (u /0])) (ren _ (lookup ρ₁ k)) ≡⟨ rensub TermD (lookup ρ₁ k) _ _ ⟩
          sub _ (lookup ρ₁ k)                           ≡⟨ sym $ Sim.sim Sim.RenSub ρ^R (lookup ρ₁ k) ⟩
          ren ρ (lookup ρ₁ k) ∎

        eq : sub ((ε ∙ u) >> th^Env th^Tm ρ₁ ρ) b ≡ ren ρ′ (sub ρ₁′ b) [ u /0]
        eq = sym $ begin
              ren ρ′ (sub ρ₁′ b) [ u /0]           ≡⟨ rensub TermD (sub ρ₁′ b) ρ′ (u /0]) ⟩
              sub (select ρ′ (u /0])) (sub ρ₁′ b)  ≡⟨ Fus.fus (Sub² TermD) ρ^R′ b ⟩
              sub ((ε ∙ u) >> th^Env th^Tm ρ₁ ρ) b ∎
\end{code}

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
open import Generic.Simulation hiding (rensub ; RenSub)
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
ren-↝-invert {Γ = Γ} {Δ} t {`λ b `∙ u} ρ eq (β {σ = σ}) =
  let (f′ , t′ , eq∙ , eqf , eqt) = ren-invert-∙ t ρ eq
      (b′ , eqλ , eqb)            = ren-invert-λ f′ ρ eqf
      eqβ : `λ b′ `∙ t′ ≡ t
      eqβ = trans (cong (_`∙ t′) eqλ) eq∙

      eq : b [ u /0] ≡ ren ρ (b′ [ t′ /0])
      eq = begin
       b [ u /0]               ≡⟨ cong₂ (λ b u → b [ u /0]) eqb eqt ⟩
       ren _ b′ [ ren ρ t′ /0] ≡⟨ sym (renβ TermD b′ t′ ρ) ⟩
       ren ρ (b′ [ t′ /0])     ∎

  in b′ [ t′ /0] , eq , subst (_↝ b′ [ t′ /0]) eqβ β
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

data SN {σ Γ} (t : Term σ Γ) : Set where
  sn : (∀ u → t ↝ u → SN u) → SN t

Red : Rel Term Unit -- predicate = binary relation with boring second component
𝓡 : ∀ {σ} → [ Term σ ⟶ κ Set ]

rel Red {α}         t _ = SN t
rel Red {σ ⇒ τ} {Γ} t _ = ∀ {Δ} (ρ : Thinning Γ Δ) {u} → 𝓡 u → 𝓡 (ren ρ t `∙ u)

𝓡 t = rel Red t _

SN-`λ : ∀ {σ τ} {Γ} {t : Term τ (σ ∷ Γ)} → SN t → SN (`λ t)
SN-`λ (sn t^R) = sn λ { u ([λ] r) → SN-`λ (t^R _ r) }

-- TODO: generic proof!
ren-id : ∀ {σ Γ} (t : Term σ Γ) → ren (base vl^Var) t ≡ t
ren-id (`var k) = cong `var (lookup-base^Var k)
ren-id (`λ t)   = cong `λ {!!}
ren-id (f `∙ t) = cong₂ _`∙_ (ren-id f) (ren-id t)

lemma2-1 : ∀ {σ τ Γ} {t : Term (σ ⇒ τ) Γ} {u : Term σ Γ} → 𝓡 t → 𝓡 u → 𝓡 (t `∙ u)
lemma2-1 {t = t} T U = subst (λ t → 𝓡 (t `∙ _)) (ren-id t) (T (base vl^Var) U)

lemma2-2 : ∀ {σ Γ Δ} (ρ : Thinning Γ Δ) {t : Term σ Γ} → SN t → SN (ren ρ t)
lemma2-2 ρ (sn U) = sn $ λ u r →
  let (u′ , eq , r′) = ren-↝-invert _ ρ refl r
  in subst SN (sym eq) $ lemma2-2 ρ (U u′ r′)

lemma2-3 : ∀ σ {Γ Δ} (ρ : Thinning Γ Δ) (t : Term σ Γ) → 𝓡 t → 𝓡 (ren ρ t)
lemma2-3 α       ρ t T = lemma2-2 ρ T
lemma2-3 (σ ⇒ τ) ρ t T = λ ρ′ U → subst (λ t → 𝓡 (t `∙ _)) (sym (ren² TermD t ρ ρ′)) (T (select ρ ρ′) U)

SN-η : ∀ {σ τ Γ} {t : Term (σ ⇒ τ) Γ} → SN (`λ (ren extend t `∙ `var z)) → SN t
SN-η (sn pr) = sn (λ u r → SN-η (pr (`λ (ren extend u `∙ `var z)) ([λ] ([∙]₂ {!!})))) -- need th-↝

data NE : ∀ {σ Γ} → Term σ Γ → Set where
  `var : ∀ {σ Γ} (k : Var σ Γ) → NE (`var k)
  _`$_ : ∀ {σ τ Γ} {f : Term (σ ⇒ τ) Γ} → NE f → (t : Term σ Γ) → NE (f `∙ t)

NE-↝ : ∀ {σ Γ} {t u : Term σ Γ} → t ↝ u → NE t → NE u
NE-↝ β        (() `$ _)
NE-↝ ([λ] r)  ()
NE-↝ ([∙]₁ r) (ne `$ _) = ne `$ _
NE-↝ ([∙]₂ r) (ne `$ t) = NE-↝ r ne `$ t

th^NE : ∀ {σ Γ Δ} {t : Term σ Γ} (ρ : Thinning Γ Δ) → NE t → NE (ren ρ t)
th^NE ρ (`var k)  = `var (lookup ρ k)
th^NE ρ (ne `$ t) = th^NE ρ ne `$ ren ρ t

SN-`∙ : ∀ {σ τ Γ} {t : Term (σ ⇒ τ) Γ} → NE t → SN t → {u : Term σ Γ} → SN u → SN (t `∙ u)
SN-`∙ t^NE t^SN u^SN = sn (aux t^NE t^SN u^SN) where

  aux : ∀ {σ τ Γ} {t : Term (σ ⇒ τ) Γ} → NE t → SN t → {u : Term σ Γ} → SN u → ∀ v → t `∙ u ↝ v → SN v
  aux ()   t^SN      u^SN      _ β
  aux t^NE t^SN      (sn u^SN) _ ([∙]₁ r) = sn (aux t^NE t^SN (u^SN _ r))
  aux t^NE (sn t^SN) u^SN      _ ([∙]₂ r) = sn (aux (NE-↝ r t^NE) (t^SN _ r) u^SN)

𝓡⇒SN : ∀ σ {Γ} (t : Term σ Γ) → 𝓡 t → SN t
NE⇒𝓡 : ∀ σ {Γ} (t : Term σ Γ) → NE t → SN t → 𝓡 t

𝓡⇒SN α       t t^R = t^R
𝓡⇒SN (σ ⇒ τ) t t^R = SN-η ηt where

  𝓡[t∙z] : 𝓡 (ren extend t `∙ `var z)
  𝓡[t∙z] = lemma2-1 (lemma2-3 _ extend t t^R) (NE⇒𝓡 σ (`var z) (`var z) (sn λ _ ()))

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

lemma2-5 : ∀ {σ τ Γ} {t : Term τ (σ ∷ Γ)} {u : Term σ Γ} → SN u → 𝓡 (t [ u /0]) → 𝓡 (`λ t `∙ u)
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

    alg^R t@((σ , τ) , true , b , refl)      {ρ₁} ρ^R (refl , refl , b^R , _)       =
      λ ρ {u} u^R →
        let bu : 𝓡 (sub ((ε ∙ u) >> th^Env th^Tm ρ₁ ρ) b)
            bu = b^R ρ (ε^R ∙^R u^R)

            ρ′  = lift vl^Var (σ ∷ []) ρ
            ρ₁′ = lift vl^Tm (σ ∷ []) ρ₁

            eq : sub ((ε ∙ u) >> th^Env th^Tm ρ₁ ρ) b ≡ ren ρ′ (sub ρ₁′ b) [ u /0]
            eq = sym $ begin
              ren ρ′ (sub ρ₁′ b) [ u /0]           ≡⟨ rensub TermD (sub ρ₁′ b) ρ′ (u /0]) ⟩
              sub (select ρ′ (u /0])) (sub ρ₁′ b)  ≡⟨ Fus.fus (Sub² TermD) {!!} b ⟩ -- technical lemma
              sub ((ε ∙ u) >> th^Env th^Tm ρ₁ ρ) b ∎

        in 𝓡 (ren ρ (sub ρ₁ (`λ b)) `∙ u) ∋ lemma2-5 (𝓡⇒SN σ u u^R)
          (𝓡 (ren ρ′ (sub ρ₁′ b) [ u /0]) ∋ subst 𝓡 eq bu)
\end{code}

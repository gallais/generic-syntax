module problem3 where

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
open import Generic.Examples.ElaborationLet

open import Data.Bool hiding (T)
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

data `Target : Set where
  Lam App : Type → Type → `Target

Target : Desc Type
Target = `σ `Target $ λ where
  (Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ ⇒ τ))
  (App σ τ) → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ))

Source : Desc Type
Source = Target `+ Let

S : Type ─Scoped
S = Tm Source _

T : Type ─Scoped
T = Tm Target _

pattern lam'  b   = (Lam _ _ , b , refl)
pattern lamS' b   = (true , lam' b)
pattern lamS  b   = `con (lamS' b)
pattern lamT  b   = `con (lam' b)
pattern app'  f t = (App _ _ , f , t , refl)
pattern appS' f t = (true , app' f t)
pattern appS  f t = `con (appS' f t)
pattern appT  f t = `con (app' f t)

pattern defS' e t = (false , _ , e , t , refl)
pattern defS  e t = `con (defS' e t)

infix 1 _⊢_∋_↝S_
data _⊢_∋_↝S_ : ∀ Γ σ → S σ Γ → S σ Γ → Set where
-- computation
  `β    : ∀ {Γ σ τ} (b : S τ (σ ∷ Γ)) u → Γ ⊢ τ ∋ appS (lamS b) u ↝S b [ u /0]
  `ζ    : ∀ {Γ σ τ} e (t : S τ (σ ∷ Γ)) → Γ ⊢ τ ∋ defS e t ↝S t [ e /0]
-- structural
  `lam  : ∀ {Γ σ τ b c} → (σ ∷ Γ) ⊢ τ ∋ b ↝S c → Γ ⊢ σ ⇒ τ ∋ lamS b ↝S lamS c
  `appl : ∀ {Γ σ τ f g} → Γ ⊢ σ ⇒ τ ∋ f ↝S g → ∀ t → Γ ⊢ τ ∋ appS f t ↝S appS g t
  `appr : ∀ {Γ σ τ t u} f → Γ ⊢ σ ∋ t ↝S u → Γ ⊢ τ ∋ appS f t ↝S appS f u

infix 1 _⊢_∋_↝T_
data _⊢_∋_↝T_ : ∀ Γ σ → T σ Γ → T σ Γ → Set where
-- computation
  `β    : ∀ {Γ σ τ} (b : T τ (σ ∷ Γ)) u → Γ ⊢ τ ∋ appT (lamT b) u ↝T b [ u /0]
-- structural
  `lam  : ∀ {Γ σ τ b c} → (σ ∷ Γ) ⊢ τ ∋ b ↝T c → Γ ⊢ σ ⇒ τ ∋ lamT b ↝T lamT c
  `appl : ∀ {Γ σ τ f g} → Γ ⊢ σ ⇒ τ ∋ f ↝T g → ∀ t → Γ ⊢ τ ∋ appT f t ↝T appT g t
  `appr : ∀ {Γ σ τ t u} f → Γ ⊢ σ ∋ t ↝T u → Γ ⊢ τ ∋ appT f t ↝T appT f u

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
  where cast = subst (_ ⊢ _ ∋ th^Tm (appT (lamT b) u) ρ ↝T_) (renβ Target b (E.ε ∙ u) ρ)

th^↝⋆T : ∀ {Γ Δ σ t u} (ρ : Thinning Γ Δ) →
         Γ ⊢ σ ∋ t ↝⋆T u → Δ ⊢ σ ∋ th^Tm t ρ ↝⋆T th^Tm u ρ
th^↝⋆T ρ Star.ε   = Star.ε
th^↝⋆T ρ (r ◅ rs) = th^↝T ρ r ◅ th^↝⋆T ρ rs

UnLet^↝⋆T : Sim ↝⋆T^R ↝⋆T^R Source UnLet UnLet
Sim.th^R  UnLet^↝⋆T = th^↝⋆T
Sim.var^R UnLet^↝⋆T = id
Sim.alg^R UnLet^↝⋆T = λ where
  (appS' f t) ρ^R (refl , refl , f^r , t^r , _) →
    gmap (λ f → appT f _) (λ r → `appl r _) f^r
   ◅◅ gmap (appT _) (`appr _) t^r
  (lamS' b)   ρ^R (refl , refl , b^r , _)       →
    gmap lamT `lam (b^r _ (pack^R (λ v → Star.ε)))
  (defS' e t) ρ^R (refl , refl , e^r , t^r , _) →
    t^r _ (ε^R ∙^R e^r)

simulation : ∀ {Γ Δ σ t u ρ ρ′} → ∀[ ↝⋆T^R ] ρ ρ′ → Γ ⊢ σ ∋ t ↝S u →
             Δ ⊢ σ ∋ unLet ρ t ↝⋆T unLet ρ′ u
simulation {Γ} {Δ} {ρ = ρ} {ρ′} ρ^R (`β b u)    =
    subst (Δ ⊢ _ ∋ _ ↝⋆T_) (sym (Fus.fus SubUnLet refl^R b))
  $ `β (unLet _ b) (unLet _ u)
  ◅_ $  subst (Δ ⊢ _ ∋_↝⋆T _) (sym (unLetSub b eq^R))
  $ Sim.sim UnLet^↝⋆T ρ∙u^R b where

  eq′^R : ∀[ Eq^R ] (select (th^Env th^Var (base vl^Var) extend) (unLet ρ u /0])) (base vl^Tm)
  lookup^R eq′^R z     = refl
  lookup^R eq′^R (s v) = cong (ren extend ∘ lookup (base vl^Tm)) (lookup-base^Var v)

  eq^R : ∀[ Eq^R ] (sub (unLet ρ u /0]) <$> (freshˡ vl^Tm Δ {_ ∷ []} >> _))
                   (unLet ρ <$> (u /0]))
  lookup^R eq^R z     = refl
  lookup^R eq^R (s v) = begin
    sub (unLet ρ u /0]) (ren (th^Env th^Var (base vl^Var) extend) (lookup ρ v))
      ≡⟨ Fus.fus (F.RenSub Target) eq′^R (lookup ρ v) ⟩
    sub (base vl^Tm) (lookup ρ v)
      ≡⟨ sub-id (lookup ρ v) ⟩
    lookup ρ v
      ≡⟨ cong (unLet ρ) (sym $ lookup-base^Tm v) ⟩
    unLet ρ (lookup (base vl^Tm) v)
      ∎

  ρ∙u^R : ∀[ ↝⋆T^R ] (unLet ρ <$> (u /0])) (unLet ρ′ <$> (u /0]))
  lookup^R ρ∙u^R z     = Sim.sim UnLet^↝⋆T ρ^R u
  lookup^R ρ∙u^R (s v) = cast $ lookup^R ρ^R v where
    cast = subst (λ v → Δ ⊢ _ ∋ unLet ρ v ↝⋆T unLet ρ′ v) (sym (lookup-base^Tm v))

simulation {ρ = ρ} {ρ′} ρ^R (`ζ e t) =
  subst (_ ⊢ _ ∋ _ ↝⋆T_) (sym (Fus.fus SubUnLet refl^R t))
  $ Sim.sim UnLet^↝⋆T ρ′^R t where

  ρ′^R : ∀[ ↝⋆T^R ] ((E.ε ∙ unLet ρ e) >> th^Env th^Tm ρ (pack id)) (unLet ρ′ <$> (e /0]))
  lookup^R ρ′^R k with split (_ ∷ []) k
  ... | inj₁ z  = Sim.sim UnLet^↝⋆T ρ^R e
  ... | inj₁ (s ())
  ... | inj₂ kʳ = cast $ lookup^R ρ^R kʳ where
    cast = subst₂ (λ v w → _ ⊢ _ ∋ v ↝⋆T unLet ρ′ w)
             (sym (ren-id′ (lookup ρ kʳ)))
             (sym (lookup-base^Tm kʳ))

simulation {Γ} {Δ} {ρ = ρ} {ρ′} ρ^R (`lam r) = gmap lamT `lam (simulation ρ′^R r) where

  ρ′^R : ∀[ ↝⋆T^R ] (freshˡ vl^Tm Δ {_ ∷ []} >> th^Env th^Tm ρ (freshʳ vl^Var (_ ∷ [])))
                    (freshˡ vl^Tm Δ {_ ∷ []} >> th^Env th^Tm ρ′ (freshʳ vl^Var (_ ∷ [])))
  lookup^R ρ′^R k with split (_ ∷ []) k
  ... | inj₁ kˡ = Star.ε
  ... | inj₂ kʳ = th^↝⋆T (th^Env th^Var (base vl^Var) extend) (lookup^R ρ^R kʳ)

simulation ρ^R (`appl r t) =
     gmap (λ f → appT f _) (λ r → `appl r _) (simulation ρ^R r)
  ◅◅ gmap (appT _) (`appr _) (Sim.sim UnLet^↝⋆T ρ^R t)
simulation ρ^R (`appr f r) =
    gmap (appT _) (`appr _) (simulation ρ^R r)
 ◅◅ gmap (λ f → appT f _) (λ r → `appl r _) (Sim.sim UnLet^↝⋆T ρ^R f)

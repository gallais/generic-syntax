\begin{code}
module Generic.Examples.ElaborationState where

open import Size
open import Data.Bool
open import Data.Product
open import Data.List.Base as L hiding ([_])
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])


open import indexed
open import var as V
open import varlike
open import environment hiding (refl)
open import Generic.Syntax hiding (TM)
open import Generic.Semantics

infixr 5 _⇒_
data MType : Set where
  α   : MType
  𝟙   : MType
  _⇒_ : MType → MType → MType
  M   : MType → MType

`APP : (A : Set) (arr : A → A → A) → Desc A
`APP A arr =  `σ A $ λ σ → `σ A $ λ τ →
              `X [] (arr σ τ) (`X [] σ (`∎ τ))

`LAM : (A : Set) (arr : A → A → A) → Desc A
`LAM A arr =  `σ A $ λ σ → `σ A $ λ τ →
               `X (σ ∷ []) τ (`∎ (arr σ τ))

StateLam : Desc MType
StateLam  =   `APP MType _⇒_
          `+  `LAM MType _⇒_
          `+  `∎ 𝟙         -- unit
          `+  `∎ (𝟙 ⇒ M α) -- get
          `+  `∎ (α ⇒ M 𝟙) -- put
          `+  `σ MType (λ σ → `∎ (σ ⇒ M σ))
          `+  `σ MType (λ σ → `σ MType $ λ τ →
               `∎ (M σ ⇒ (σ ⇒ M τ) ⇒ M τ))

data PType : Set where
  α   : PType
  𝟙   : PType
  _⇒_ : PType → PType → PType
  _⊗_ : PType → PType → PType

ProdLam : Desc PType
ProdLam  =    `APP PType _⇒_
         `+  `LAM PType _⇒_
         `+  (`σ PType $ λ σ → `σ PType $ λ τ → -- pair
              `X [] σ (`X [] τ (`∎ (σ ⊗ τ))))
         `+  (`σ PType $ λ σ → `σ PType $ λ τ → -- fst
             `X [] (σ ⊗ τ) (`∎ σ))
         `+  (`σ PType $ λ σ → `σ PType $ λ τ → -- snd
             `X [] (σ ⊗ τ) (`∎ τ))
         `+  `∎ 𝟙                                -- unit

TM : PType → List PType → Set
TM = Tm ProdLam ∞

APP : {σ τ : PType} → [ TM (σ ⇒ τ) ⟶ TM σ ⟶ TM τ ]
APP f t = `con (true , _ , _ , f , t , refl)

LAM : {σ τ : PType} → [ (σ ∷_) ⊢ TM τ ⟶ TM (σ ⇒ τ) ]
LAM b = `con (false , true , _ , _ , b , refl)

PAIR : {σ τ : PType} → [ TM σ ⟶ TM τ ⟶ TM (σ ⊗ τ) ]
PAIR a b = `con (false , false , true , _ , _ , a , b , refl)

FST : {σ τ : PType} → [ TM (σ ⊗ τ) ⟶ TM σ ]
FST p = `con (false , false , false , true , _ , _ , p , refl)

SND : {σ τ : PType} → [ TM (σ ⊗ τ) ⟶ TM τ ]
SND p = `con (false , false , false , false , true , _ , _ , p , refl)

UNIT : [ TM 𝟙 ]
UNIT = `con (false , false , false , false , false , refl)


M⟦_⟧ : MType → PType
M⟦ α     ⟧ = α
M⟦ 𝟙     ⟧ = 𝟙
M⟦ σ ⇒ τ ⟧ = M⟦ σ ⟧ ⇒ M⟦ τ ⟧
M⟦ M σ   ⟧ = α ⇒ (α ⊗ M⟦ σ ⟧)

⇒-inj : {σ τ σ₁ τ₁ : PType} → (PType ∋ σ ⇒ τ) ≡ σ₁ ⇒ τ₁ → σ ≡ σ₁ × τ ≡ τ₁
⇒-inj refl = refl , refl

⊗-inj : {σ τ σ₁ τ₁ : PType} → (PType ∋ σ ⊗ τ) ≡ σ₁ ⊗ τ₁ → σ ≡ σ₁ × τ ≡ τ₁
⊗-inj refl = refl , refl

M⟦⟧-inj : Injective M⟦_⟧
M⟦⟧-inj = record { inj = go _ _ } where
  go : (σ τ : MType) → M⟦ σ ⟧ ≡ M⟦ τ ⟧ → σ ≡ τ
  go α α eq = refl
  go α 𝟙 ()
  go α (τ ⇒ τ₁) ()
  go α (M τ) ()
  go 𝟙 α ()
  go 𝟙 𝟙 eq = refl
  go 𝟙 (τ ⇒ τ₁) ()
  go 𝟙 (M τ) ()
  go (σ ⇒ σ₁) α ()
  go (σ ⇒ σ₁) 𝟙 ()
  go (σ ⇒ σ₁) (τ ⇒ τ₁) eq =
    cong₂ _⇒_ (go σ τ (proj₁ (⇒-inj eq))) (go σ₁ τ₁ (proj₂ (⇒-inj eq)))
  go (σ ⇒ α) (M τ) ()
  go (σ ⇒ 𝟙) (M τ) ()
  go (σ ⇒ (σ₁ ⇒ σ₂)) (M τ) ()
  go (σ ⇒ M σ₁) (M τ) ()
  go (M σ) α ()
  go (M σ) 𝟙 ()
  go (M σ) (τ ⇒ α) ()
  go (M σ) (τ ⇒ 𝟙) ()
  go (M σ) (τ ⇒ (τ₁ ⇒ τ₂)) ()
  go (M σ) (τ ⇒ M τ₁) ()
  go (M σ) (M τ) eq = cong M (go σ τ (proj₂ (⊗-inj (proj₂ (⇒-inj eq)))))

MTM : MType → List MType → Set
MTM σ Γ = TM M⟦ σ ⟧ (L.map M⟦_⟧ Γ)

MVAR : MType → List MType → Set
MVAR σ Γ = Var M⟦ σ ⟧ (L.map M⟦_⟧ Γ)

vl^MVAR : VarLike MVAR
vl^MVAR = record
  { new   = z
  ; th^𝓥  = λ {σ} v ρ → M⟦_⟧ V.<$> lookup ρ {σ} (M⟦⟧-inj <$>⁻¹ v) }

Elab^State : Sem StateLam MVAR MTM
Elab^State = record
  { th^𝓥  = λ {σ} → th^𝓥 vl^MVAR {σ}
  ; var   = `var
  ; alg   = case ⟦app⟧
          $ case ⟦lam⟧
          $ case (λ where refl → UNIT)
          $ case (λ where refl → LAM (LAM (PAIR (`var z) (`var z))))
          $ case (λ where refl → LAM (LAM (PAIR (`var (s z)) UNIT)))
          $ case (λ where (σ , refl) → LAM (LAM (PAIR (`var z) (`var (s z)))))
          (λ where (σ , τ , refl) → LAM (LAM (LAM
                     let p = APP (`var (s (s z))) (`var z)
                     in APP (APP (`var (s z)) (SND p)) (FST p))))
  } where

  ⟦X⟧ : List MType → MType → List MType → Set
  ⟦X⟧ = Kripke MVAR MTM

  ⟦app⟧ : {σ : MType} → [ ⟦ `APP MType _⇒_ ⟧ ⟦X⟧ σ ⟶ MTM σ ]
  ⟦app⟧ (_ , _ , f , t , refl) = APP f t

  ⟦lam⟧ : {σ : MType} → [ ⟦ `LAM MType _⇒_ ⟧ ⟦X⟧ σ ⟶ MTM σ ]
  ⟦lam⟧ (σ , τ , b , refl) = LAM (reify {𝓒 = MTM} vl^MVAR (σ ∷ []) τ b)
\end{code}

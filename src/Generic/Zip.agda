module Generic.Zip where

open import Size
open import Data.Unit
open import Data.List hiding ([_] ; zip)
open import Data.Product hiding (zip ; ,_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import indexed
open import rel
open import varlike
open import environment
open import Generic.Syntax
open import Generic.Semantics

module _ {I : Set} {X Y : List I → I → List I → Set} where

 Zip :  (d : Desc I) (R : (δ : List I) (i : I) → [ X δ i ⟶ Y δ i ⟶ κ Set ]) →
        {i : I} → [ ⟦ d ⟧ X i ⟶ ⟦ d ⟧ Y i ⟶ κ Set ]
 Zip (`∎ i′)     R x        y         = ⊤
 Zip (`X δ j d)  R (r , x)  (r' , y)  = R δ j r r' × Zip d R x y
 Zip (`σ A d)    R (a , x)  (a' , y)  = Σ[ eq ∈ a' ≡ a ] Zip (d a) R x (rew eq y)
   where rew = subst (λ a → ⟦ d a ⟧ _ _ _)

module _ {I : Set} {X Y T : List I → I → List I → Set}
         {P : ∀ δ i → [ X δ i ⟶ Y δ i ⟶ κ Set ]} where
 zip : (d : Desc I) {γ γ′ : List I}
       {f : ∀ δ i → T δ i γ → X δ i γ′} {g : ∀ δ i → T δ i γ → Y δ i γ′}
       (FG : ∀ δ i → (t : T δ i γ) → P δ i (f δ i t) (g δ i t)) →
       {i : I} (t : ⟦ d ⟧ T i γ) → Zip d P (fmap d f t) (fmap d g t)
 zip (`σ A d)    FG (a , t)  = refl , zip (d a) FG t
 zip (`X δ i d)  FG (r , t)  = FG δ i r , zip d FG t
 zip (`∎ i′)     FG t        = tt

module _ {I : Set} {X : List I → I → List I → Set}
         {P : ∀ δ i → [ X δ i ⟶ X δ i ⟶ κ Set ]} where

 refl^Zip :  (refl^P : ∀ δ i {γ} (x : X δ i γ) → P δ i x x) →
             (d : Desc I) {i : I} {γ : List I} (t : ⟦ d ⟧ X i γ) →
             Zip d P t t
 refl^Zip refl^P (`σ A d)    (a , t)  = refl , refl^Zip refl^P (d a) t
 refl^Zip refl^P (`X δ i d)  (r , t)  = refl^P δ i r , refl^Zip refl^P d t
 refl^Zip refl^P (`∎ i′)      t       = tt

 sym^Zip :  (sym^P : ∀ δ i {γ} {x y : X δ i γ} → P δ i x y → P δ i y x) →
            (d : Desc I) {i : I} {γ : List I} {t u : ⟦ d ⟧ X i γ} →
            Zip d P t u → Zip d P u t
 sym^Zip sym^P (`σ A d)    (refl  , eq)  = refl , sym^Zip sym^P (d _) eq
 sym^Zip sym^P (`X δ i d)  (prs       , eq)  = sym^P δ i prs , sym^Zip sym^P d eq
 sym^Zip sym^P (`∎ i′)      eq                = tt

 trans^Zip :  (trans^P : ∀ δ i {γ} {x y z : X δ i γ} → P δ i x y  → P δ i y z → P δ i x z)
              (d : Desc I) {i : I} {γ : List I} {t u v : ⟦ d ⟧ X i γ} →
              Zip d P t u → Zip d P u v → Zip d P t v
 trans^Zip trans^P (`σ A d)  (refl  , t≈u) (refl , u≈v) =
   refl , trans^Zip trans^P (d _) t≈u u≈v
 trans^Zip trans^P (`X δ i d)  (prs       , t≈u) (psq      , u≈v) =
   trans^P δ i prs psq , trans^Zip trans^P d t≈u u≈v
 trans^Zip trans^P (`∎ i′)         _                 _             = tt


module _ {I : Set} {𝓥₁ 𝓥₂ 𝓒 : I → List I → Set} (𝓡^𝓥  : Rel 𝓥₁ 𝓥₂) where

 zip^reify : {Γ : List I}  {vl^𝓥₁ : VarLike 𝓥₁} {vl^𝓥₂ : VarLike 𝓥₂}
             (eq : (Δ : List I) (σ : I) {t₁ : Kripke 𝓥₁ 𝓒 Δ σ Γ} {t₂ : Kripke 𝓥₂ 𝓒 Δ σ Γ} →
                   Kripke^R 𝓡^𝓥 (mkRel _≡_) Δ σ t₁ t₂ →
                   reify vl^𝓥₁ Δ σ t₁ ≡ reify vl^𝓥₂ Δ σ t₂) →
             (d : Desc I) {σ : I} {b₁ : ⟦ d ⟧ (Kripke 𝓥₁ 𝓒) σ Γ} {b₂ : ⟦ d ⟧ (Kripke 𝓥₂ 𝓒) σ Γ} →
             Zip d (Kripke^R 𝓡^𝓥 (mkRel _≡_)) b₁ b₂ →
             fmap {X = Kripke 𝓥₁ 𝓒} {Y = Scope 𝓒} d (reify vl^𝓥₁) b₁ ≡ fmap d (reify vl^𝓥₂) b₂
 zip^reify eq (`σ A d)    (refl , zp)  = cong (_ ,_) (zip^reify eq (d _) zp)
 zip^reify eq (`X δ i d)  (r , zp)         = cong₂ _,_ (eq δ i r) (zip^reify eq d zp)
 zip^reify eq (`∎ i′)      zp               = uip _ _ where
   uip : ∀ {A : Set} {a b : A} (p q : a ≡ b) → p ≡ q
   uip refl refl = refl


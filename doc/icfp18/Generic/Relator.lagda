\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Relator where

open import Axiom.UniquenessOfIdentityProofs.WithK
open import Size
open import Data.Unit
open import Data.List hiding ([_] ; zip)
open import Data.Product hiding (zip)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Function
open import Relation.Unary
open import Data.Var
open import Data.Var.Varlike
open import Data.Environment
open import Generic.Syntax
open import Generic.Semantics

private
  variable
    I : Set
    T X Y Z : List I → I ─Scoped
    γ δ θ : List I
    σ τ : I
    𝓥 𝓦 𝓒 : I ─Scoped

\end{code}
%<*ziptype>
\begin{code}
⟦_⟧ᴿ : (d : Desc I)  → (∀ Δ σ → ∀[ X Δ σ ⇒ Y Δ σ ⇒ const Set ])
                     → ∀[ ⟦ d ⟧ X σ ⇒ ⟦ d ⟧ Y σ ⇒ const Set ]
⟦ `∎ j      ⟧ᴿ R x        y         = ⊤
⟦ `X Δ j d  ⟧ᴿ R (r , x)  (r' , y)  = R Δ j r r' × ⟦ d ⟧ᴿ R x y
⟦ `σ A d    ⟧ᴿ R (a , x)  (a' , y)  = Σ (a' ≡ a) λ where refl → ⟦ d a ⟧ᴿ R x y
\end{code}
%</ziptype>
\begin{code}

module _
  {R : ∀ θ σ → ∀[ X θ σ ⇒ Y θ σ ⇒ const Set ]}
  {f : ∀ θ σ → T θ σ γ → X θ σ δ}
  {g : ∀ θ σ → T θ σ γ → Y θ σ δ}
  where

  liftᴿ : ∀ d (FG : ∀ θ σ t → R θ σ (f θ σ t) (g θ σ t)) →
          ∀ (t : ⟦ d ⟧ T σ γ) → ⟦ d ⟧ᴿ R (fmap d f t) (fmap d g t)
  liftᴿ (`σ A d)    FG (a , t)  = refl , liftᴿ (d a) FG t
  liftᴿ (`X j Δ d)  FG (x , t)  = FG j Δ x , liftᴿ d FG t
  liftᴿ (`∎ j)      FG refl     = tt

module _ {R : ∀ θ σ → ∀[ X θ σ ⇒ X θ σ ⇒ const Set ]} where

  reflᴿ :  ∀ d (re : ∀ θ σ (x : X θ σ γ) → R θ σ x x) →
           (t : ⟦ d ⟧ X σ γ) → ⟦ d ⟧ᴿ R t t
  reflᴿ (`σ A d)    re (a , t)  = refl , reflᴿ (d a) re t
  reflᴿ (`X j Δ d)  re (x , t)  = re j Δ x , reflᴿ d re t
  reflᴿ (`∎ j)      re refl     = tt

module _ {R : ∀ θ σ → ∀[ X θ σ ⇒ Y θ σ ⇒ const Set ]}
         {S : ∀ θ σ → ∀[ Y θ σ ⇒ X θ σ ⇒ const Set ]}
         where

  symᴿ :  ∀ d (sy : ∀ θ σ {x : X θ σ γ} {y} → R θ σ x y → S θ σ y x) →
          ∀ {t : ⟦ d ⟧ X σ γ} {u} → ⟦ d ⟧ᴿ R t u → ⟦ d ⟧ᴿ S u t
  symᴿ (`σ A d)    sy (refl , t)  = refl , symᴿ (d _) sy t
  symᴿ (`X j Δ d)  sy (r    , t)  = sy j Δ r , symᴿ d sy t
  symᴿ (`∎ j)      sy tt          = tt

module _ {R  : ∀ θ σ → ∀[ X θ σ ⇒ Y θ σ ⇒ const Set ]}
         {S  : ∀ θ σ → ∀[ Y θ σ ⇒ Z θ σ ⇒ const Set ]}
         {RS : ∀ θ σ → ∀[ X θ σ ⇒ Z θ σ ⇒ const Set ]}
         where

  transᴿ : ∀ d (tr : ∀ θ σ {x : X θ σ γ} {y z} → R θ σ x y → S θ σ y z → RS θ σ x z) →
           ∀ {t : ⟦ d ⟧ X σ γ} {u v} → ⟦ d ⟧ᴿ R t u → ⟦ d ⟧ᴿ S u v → ⟦ d ⟧ᴿ RS t v
  transᴿ (`σ A d)    tr (refl , t)  (refl , u)  = refl , transᴿ (d _) tr t u
  transᴿ (`X j Δ d)  tr (x , t)     (y , u)     = tr j Δ x y , transᴿ d tr t u
  transᴿ (`∎ j)      tr tt          tt          = tt


open import Data.Relation

module _ (𝓥ᴿ : Rel {I} 𝓥 𝓦) {vl^𝓥 : VarLike 𝓥} {vl^𝓦 : VarLike 𝓦} where

  reifyᴿ : ∀ d (re : ∀ θ σ {v : Kripke 𝓥 𝓒 θ σ γ} {w} →
                     Kripkeᴿ 𝓥ᴿ Eqᴿ θ σ v w →
                     reify vl^𝓥 θ σ v ≡ reify vl^𝓦 θ σ w) →
           ∀ {bv : ⟦ d ⟧ (Kripke 𝓥 𝓒) σ γ} {bw : ⟦ d ⟧ (Kripke 𝓦 𝓒) σ γ} →
           ⟦ d ⟧ᴿ (Kripkeᴿ 𝓥ᴿ Eqᴿ) bv bw →
           (⟦ d ⟧ (Scope 𝓒) σ γ ∋ fmap d (reify vl^𝓥) bv) ≡ fmap d (reify vl^𝓦) bw
  reifyᴿ (`σ A d)    re (refl , t)  = cong -,_ (reifyᴿ (d _) re t)
  reifyᴿ (`X j Δ d)  re (x , t)     = cong₂ _,_ (re j Δ x) (reifyᴿ d re t)
  reifyᴿ (`∎ j)      re tt          = uip _ _
\end{code}

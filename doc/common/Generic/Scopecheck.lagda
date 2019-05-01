\begin{code}
{-# OPTIONS --safe --sized-types #-}

open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality

open import Generic.Syntax

module Generic.Scopecheck
       {E I : Set} {d : Desc I} (I-dec : Decidable {A = I} _≡_) where

open import Category.Monad

open import Level
open import Size
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)

open import Data.Product
open import Data.String as String using (String)
open import Data.Sum
import Data.Sum.Categorical.Left as SC
open import Function
open import Relation.Nullary

open import Data.Var hiding (_<$>_)

private
  variable
    σ : I
    Γ Δ : List I
    i : Size

Names : List I → Set
Names = All (const String)

WithNames : (I → Set) → List I → I ─Scoped
WithNames T []  j Γ = T j
WithNames T Δ   j Γ = Names Δ × T j

data Raw : Size → I → Set where
  `var : E → String → Raw (↑ i) σ
  `con : ⟦ d ⟧ (WithNames (Raw i)) σ [] → Raw (↑ i) σ

private
  M : Set → Set
  M = (E × String) ⊎_
open RawMonad (SC.monad (E × String) zero)

instance _ =  rawIApplicative

var : E → String → ∀ σ Γ → Names Γ → M (Var σ Γ)
var e str σ []       []         = inj₁ (e , str)
var e str σ (τ ∷ Γ)  (nm ∷ scp) with nm String.≟ str
... | no ¬p = s <$> var e str σ Γ scp
... | yes p with I-dec σ τ
... | no ¬eq   = inj₁ (e , str)
... | yes refl = inj₂ z

toTm     : Names Γ → Raw i σ → M (Tm d i σ Γ)
toScope  : Names Γ → ∀ Δ σ → WithNames (Raw i) Δ σ [] → M (Scope (Tm d i) Δ σ Γ)

toTm scp (`var e v) = `var <$> var e v _ _ scp
toTm scp (`con b)   = `con <$> mapA d (toScope scp) b

toScope scp []        σ b         = toTm scp b
toScope scp Δ@(_ ∷ _) σ (nms , b) = toTm (++⁺ nms scp) b
\end{code}

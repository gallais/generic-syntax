\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Data.Relation where

open import Size
open import Data.Sum
open import Data.List.Base hiding (lookup ; [_])

open import Data.Var hiding (_<$>_)
open import Data.Environment
open import Generic.Syntax
open import Relation.Unary hiding (U)
open import Agda.Builtin.Equality
open import Function

private
  variable
    I : Set
    σ : I
    T U : I ─Scoped
    𝓥ᴬ 𝓥ᴮ : I ─Scoped
    Γ Δ : List I

\end{code}
%<*rel>
\begin{code}
record Rel (T U : I ─Scoped) : Set₁ where
  constructor mkRel
  field rel : ∀ σ → ∀[ T σ ⇒ U σ ⇒ const Set ]
\end{code}
%</rel>
\begin{code}
open Rel public

\end{code}
%<*all>
\begin{code}
record All  (𝓥ᴿ : Rel 𝓥ᴬ 𝓥ᴮ) (Γ : List I)
            (ρᴬ : (Γ ─Env) 𝓥ᴬ Δ) (ρᴮ : (Γ ─Env) 𝓥ᴮ Δ) : Set where
  constructor packᴿ
  field lookupᴿ : ∀ k → rel 𝓥ᴿ σ (lookup ρᴬ k) (lookup ρᴮ k)
\end{code}
%</all>
\begin{code}
open All public

module _ {T U : I ─Scoped} {𝓡 : Rel T U} where

  private
    variable
      ρᵀ σᵀ : (Γ ─Env) T Δ
      ρᵁ σᵁ : (Γ ─Env) U Δ
      vᵀ : T σ Γ
      vᵁ : U σ Γ
      fᵀ : ∀ {i} → T i Γ → T i Δ
      fᵁ : ∀ {i} → U i Γ → U i Δ

  εᴿ : All 𝓡 [] ρᵀ ρᵁ
  lookupᴿ εᴿ ()

  infixl 20 _∙ᴿ_ _∷ᴿ_
  _∙ᴿ_ :  All 𝓡 Γ ρᵀ ρᵁ → rel 𝓡 σ vᵀ vᵁ → All 𝓡 (σ ∷ Γ) (ρᵀ ∙ vᵀ) (ρᵁ ∙ vᵁ)
  lookupᴿ (ρ ∙ᴿ v) z      = v
  lookupᴿ (ρ ∙ᴿ v) (s k)  = lookupᴿ ρ k

  _∷ᴿ_ :  rel 𝓡 σ (lookup ρᵀ z) (lookup ρᵁ z) →
          (∀ {σ} (v : Var σ Γ) → rel 𝓡 _ (lookup ρᵀ (s v)) (lookup ρᵁ (s v))) →
          All 𝓡 (σ ∷ Γ) ρᵀ ρᵁ
  lookupᴿ (v ∷ᴿ ρ) z      = v
  lookupᴿ (v ∷ᴿ ρ) (s k)  = ρ k

  _>>ᴿ_ :  All 𝓡 Γ ρᵀ ρᵁ → All 𝓡 Δ σᵀ σᵁ →
           All 𝓡 (Γ ++ Δ) (ρᵀ >> σᵀ) (ρᵁ >> σᵁ)
  lookupᴿ (_>>ᴿ_ {Γ} ρᴿ σᴿ) k with split Γ k
  ... | inj₁ k₁ = lookupᴿ ρᴿ k₁
  ... | inj₂ k₂ = lookupᴿ σᴿ k₂

  selectᴿ : ∀ ρ → All 𝓡 Δ ρᵀ ρᵁ → All 𝓡 Γ (select ρ ρᵀ) (select ρ ρᵁ)
  lookupᴿ (selectᴿ ρ ρᴿ) k = lookupᴿ ρᴿ (lookup ρ k)

  _<$>ᴿ_ : (∀ {i t u} → rel 𝓡 i t u → rel 𝓡 i (fᵀ t) (fᵁ u)) →
           All 𝓡 Γ ρᵀ ρᵁ → All 𝓡 Γ (fᵀ <$> ρᵀ) (fᵁ <$> ρᵁ)
  lookupᴿ (F <$>ᴿ ρ) k = F (lookupᴿ ρ k)

module _ {T : I ─Scoped} where

  private
    variable
      ρ : (Γ ─Env) T Δ

\end{code}
%<*eqR>
\begin{code}
  Eqᴿ : Rel T T
  rel Eqᴿ i = _≡_
\end{code}
%</eqR>
%<*reflR>
\begin{code}
  reflᴿ : All Eqᴿ Γ ρ ρ
  lookupᴿ reflᴿ k = refl
\end{code}
%</reflR>
\begin{code}

module _ {A B : I ─Scoped} where

  open import Relation.Binary.HeterogeneousEquality.Core

  HEqᴿ : Rel A B
  rel HEqᴿ i = λ a b → a ≅ b

module _ {d : Desc I} where

 VarTmᴿ : Rel Var (Tm d ∞)
 rel VarTmᴿ i v t = `var v ≡ t
\end{code}

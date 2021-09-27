{-# OPTIONS --safe --sized-types #-}

module Generic.Syntax.STLC+Product where

open import Data.Product
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Function
open import Relation.Unary

open import Data.Var
open import Data.Environment
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic

infixr 5 _`→_
infixr 6 _⊗_
data PType : Set where
  α   : PType
  𝟙   : PType
  _`→_ : PType → PType → PType
  _⊗_ : PType → PType → PType


data `STLCPr : Set where
  -- Application and Lambda-astraction
  App : PType → PType → `STLCPr
  Lam : PType → PType → `STLCPr
  -- Pair constructors
  Prd : PType → PType → `STLCPr
  Fst : PType → PType → `STLCPr
  Snd : PType → PType → `STLCPr
  -- Unit constructor
  One : `STLCPr

STLCPr : Desc PType
STLCPr = `σ `STLCPr $ λ where
  (App σ τ) → `X [] (σ `→ τ) (`X [] σ (`∎ τ))
  (Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ `→ τ))
  (Prd σ τ) → `X [] σ (`X [] τ (`∎ (σ ⊗ τ)))
  (Fst σ τ) → `X [] (σ ⊗ τ) (`∎ σ)
  (Snd σ τ) → `X [] (σ ⊗ τ) (`∎ τ)
  One       → `∎ 𝟙

module PATTERNS where

  pattern APP f t = `con (App _ _ , f , t , refl)
  pattern LAM b   = `con (Lam _ _ , b , refl)
  pattern PRD a b = `con (Prd _ _ , a , b , refl)
  pattern FST p   = `con (Fst _ _ , p , refl)
  pattern SND p   = `con (Snd _ _ , p , refl)
  pattern ONE     = `con (One , refl)

  CUR : ∀ {σ τ ν} → ∀[ Tm STLCPr _ (σ `→ τ `→ ν) ⇒ Tm STLCPr _ (σ ⊗ τ `→ ν) ]
  CUR t = LAM (APP (APP (ren weaken t) (FST (`var z))) (SND (`var z)))

  SWP : ∀ {σ τ} → ∀[ Tm STLCPr _ (σ ⊗ τ) ⇒ Tm STLCPr _ (τ ⊗ σ) ]
  SWP t = PRD (SND t) (FST t)

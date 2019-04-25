{-# OPTIONS --safe --sized-types #-}

module Generic.Syntax.STLC+State where

open import Data.Product
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Function

open import Data.Var
open import Generic.Syntax

infixr 5 _`→_
data MType : Set where
  α   : MType
  𝟙   : MType
  _`→_ : MType → MType → MType
  M   : MType → MType

data `STLCSt : Set where
  -- Application and Lambda Abstraction
  App : MType → MType → `STLCSt
  Lam : MType → MType → `STLCSt
  -- Unit
  One : `STLCSt
  -- State Operations: Get & Put
  Get : `STLCSt
  Put : `STLCSt
  -- Monadic Operations: Return, Bind
  Ret : MType → `STLCSt
  Bnd : MType → MType → `STLCSt

STLCSt : Desc MType
STLCSt = `σ `STLCSt $ λ where
  (App σ τ) → `X [] (σ `→ τ) (`X [] σ (`∎ τ))
  (Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ `→ τ))
  One       → `∎ 𝟙
  Get       → `∎ (M α)
  Put       → `X [] α (`∎ (M 𝟙))
  (Ret σ)   → `X [] σ (`∎ (M σ))
  (Bnd σ τ) → `X [] (M σ) (`X [] (σ `→ M τ) (`∎ (M τ)))

module PATTERNS where

  infixr -1 _>>=_
  pattern APP f t   = `con (App _ _ , f , t , refl)
  pattern LAM b     = `con (Lam _ _ , b , refl)
  pattern ONE       = `con (One , refl)
  pattern GET       = `con (Get , refl)
  pattern PUT t     = `con (Put , t , refl)
  pattern RET t     = `con (Ret _ , t , refl)
  pattern _>>=_ m f = `con (Bnd _ _ , m , f , refl)

-- get >>= λ x → put x >> put x >> return ()
_ : TM STLCSt (M 𝟙)
_ = let open PATTERNS in
    GET              >>= LAM $′
    PUT (`var z)     >>= LAM $′
    PUT (`var (s z)) >>= LAM $′
    RET ONE

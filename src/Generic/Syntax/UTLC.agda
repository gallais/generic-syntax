module Generic.Syntax.UTLC where

open import Size
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Function

open import var
open import Generic.Syntax

-- Two constructors: Application and Lambda-abstraction
data `UTLC : Set where App Lam : `UTLC

UTLC : Desc ⊤
UTLC =  `σ `UTLC $ λ where
  App → `X [] tt (`X [] tt (`∎ tt))
  Lam → `X (tt ∷ []) tt (`∎ tt)

module PATTERNS where

  pattern VAR x    = `var x
  pattern APP f t  = `con (App , f , t , refl)
  pattern LAM b    = `con (Lam , b , refl)

`id : TM UTLC tt
`id = let open PATTERNS in LAM (VAR z)

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
UTLC : Desc ⊤
UTLC =  `X [] tt (`X [] tt (`∎ tt))
     `+ `X (tt ∷ []) tt (`∎ tt)

pattern `V x    = `var x
pattern `A f t  = `con (true , f , t , refl)
pattern `L b    = `con (false , b , refl)

`id : TM UTLC tt
`id = `L (`V z)

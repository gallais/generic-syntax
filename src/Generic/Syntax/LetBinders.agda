module Generic.Syntax.LetBinders where

open import Data.Product
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Function

open import Generic.Syntax

module _ {I : Set} where

  Lets : Desc I
  Lets = `σ (List I × I) $ uncurry $ λ Δ σ →
         `Xs Δ (`X Δ σ (`∎ σ))

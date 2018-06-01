module Generic.Syntax.LetBinder where

open import Data.Product
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Function

open import var
open import Generic.Syntax

module _ {I : Set} where

  Let : Desc I
  Let = `σ (I × I) $ uncurry $ λ σ τ →
        `X [] σ (`X (σ ∷ []) τ (`∎ τ))

pattern `IN' e t = (_ , e , t , refl)
pattern `IN  e t = `con (`IN' e t)

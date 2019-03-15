module Generic.Syntax.LetBinder where

open import Data.Bool
open import Data.Product
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Function

open import indexed
open import var
open import Generic.Syntax

module _ {I : Set} where

  Let : Desc I
  Let = `σ (I × I) $ uncurry $ λ σ τ →
        `X [] σ (`X (σ ∷ []) τ (`∎ τ))

pattern `IN' e t = (_ , e , t , refl)
pattern `IN  e t = `con (`IN' e t)

module _ {I : Set} {d : Desc I} where

  embed : ∀ {i σ} → [ Tm d i σ ⟶ Tm (d `+ Let) i σ ]
  embed = map^Tm (MkDescMorphism (true ,_))

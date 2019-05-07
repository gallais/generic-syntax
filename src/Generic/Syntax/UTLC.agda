{-# OPTIONS --safe --sized-types #-}

module Generic.Syntax.UTLC where

open import Size
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.List.Base hiding ([_])
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Var
open import Generic.Syntax


UTLC : Desc ⊤
UTLC = `σ Bool $ λ isApp → if isApp
  then  `X [] tt (`X [] tt (`∎ tt))
  else  `X (tt ∷ []) tt (`∎ tt)

private
  module DISPLAYONLY where

    pattern `app f t  = `con (true , f , t , refl)
    pattern `lam b    = `con (false , b , refl)

pattern `app' f t  = (true , f , t , refl)
pattern `lam' b    = (false , b , refl)
pattern `app  f t  = `con (`app' f t)
pattern `lam  b    = `con (`lam' b)

id^U : Tm UTLC ∞ tt []
id^U = `lam (`var z)

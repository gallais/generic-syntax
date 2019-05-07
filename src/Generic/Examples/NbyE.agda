{-# OPTIONS --sized-types #-}

module Generic.Examples.NbyE where

open import Size
open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe
open import Data.Product
open import Data.Unit
open import Function
open import Relation.Unary
open import Relation.Binary.PropositionalEquality

open import Data.Var.Varlike
open import Data.Environment
open import Generic.Syntax
open import Generic.Syntax.UTLC
open import Generic.Semantics.NbyE


pattern LAM  f   = C (false , f , refl)
pattern APP' f t = (true , f , t , refl)

norm^LC : ∀[ Tm UTLC ∞ tt ⇒ Maybe ∘ Tm UTLC ∞ tt ]
norm^LC = norm $ λ where
  (APP' (LAM f) t)  → extract f (ε ∙ t)  -- redex
  t                 → C t                -- value

open import Relation.Binary.PropositionalEquality hiding ([_] ; refl)


_ : norm^LC (`app id^U (`app id^U id^U)) ≡ just id^U
_ = refl

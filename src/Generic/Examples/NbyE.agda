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


norm^LC : ∀[ Tm UTLC ∞ tt ⇒ Maybe ∘ Tm UTLC ∞ tt ]
norm^LC = norm $ case app (C ∘ (false ,_)) where

  Model = Dm UTLC ∞

  app : ∀[ ⟦ `X [] tt (`X [] tt (`∎ tt)) ⟧ (Kripke Model Model) tt ⇒ Model tt ]
  app (C (false , f , _)  , t  , _) = f (base vl^Var) (ε ∙ t)  -- redex
  app (f                  , t  , _) = C (true , f , t , refl)  -- stuck application

open import Relation.Binary.PropositionalEquality hiding ([_] ; refl)

_ : norm^LC (`app `id (`app `id `id)) ≡ just `id
_ = refl

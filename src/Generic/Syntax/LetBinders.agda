{-# OPTIONS --safe --sized-types #-}

module Generic.Syntax.LetBinders where

open import Data.Bool
open import Data.Product
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Function
open import Relation.Unary

open import Generic.Syntax

module _ {I : Set} where

  Lets : Desc I
  Lets = `σ (List I × I) $ uncurry $ λ Δ σ →
         `Xs Δ (`X Δ σ (`∎ σ))

module _ {I : Set} {d : Desc I} where

  embed : ∀ {i σ} → ∀[ Tm d i σ ⇒ Tm (d `+ Lets) i σ ]
  embed = map^Tm (MkDescMorphism (true ,_))

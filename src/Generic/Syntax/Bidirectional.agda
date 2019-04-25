{-# OPTIONS --safe --sized-types #-}

module Generic.Syntax.Bidirectional where

open import Data.Product
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Function

open import Generic.Syntax

open import StateOfTheArt.ACMM using (Type; α; _`→_) public

-- We have an *untyped* language presented in a bidirectional manner
-- where phases are statically checked

data `Lang : Set where
  App Lam Emb : `Lang
  Cut : Type → `Lang

data Mode : Set where
  Check Infer : Mode

-- On top of the traditional Application and Lambda-Abstraction constructors,
-- we have two change of direction ones: `Emb` which takes inferable terms and
-- makes them checkable (it is enough to compare the inferred type to the
-- candidate provided); and `Cut` which takes a checkable term and makes it
-- inferrable thanks to a type-annotation.

Lang : Desc Mode
Lang  =  `σ `Lang $ λ where
  App      → `X [] Infer (`X [] Check (`∎ Infer))
  Lam      → `X (Infer ∷ []) Check (`∎ Check)
  (Cut σ)  → `X [] Check (`∎ Infer)
  Emb      → `X [] Infer (`∎ Check)

module PATTERNS where

  pattern APP f t  = `con (App , f , t , refl)
  pattern LAM b    = `con (Lam , b , refl)
  pattern CUT σ t  = `con (Cut σ , t , refl)
  pattern EMB t    = `con (Emb , t , refl)

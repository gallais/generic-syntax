{-# OPTIONS --safe --sized-types #-}

module Generic.Semantics.Elaboration.LetBinders where

open import Size
open import Data.Product
open import Function
open import Relation.Unary
open import Relation.Binary.PropositionalEquality

open import Data.Environment
open import Generic.Syntax
open import Generic.Syntax.LetBinders
open import Generic.Semantics
open import Generic.Semantics.Syntactic

module _ {I : Set} {d : Desc I} where

  private
    variable
      σ : I
      i : Size

  UnLets : Semantics (d `+ Lets) (Tm d _) (Tm d _)
  Semantics.th^𝓥  UnLets = th^Tm
  Semantics.var   UnLets = id
  Semantics.alg   UnLets = case (Semantics.alg Sub) $ λ where
    ((Δ , σ) , est) → case unXs Δ est of λ where
       (es , t , refl) → t $$ es

  unLets : ∀[ Tm (d `+ Lets) i σ ⇒ Tm d _ σ ]
  unLets = Semantics.semantics UnLets id^Tm 

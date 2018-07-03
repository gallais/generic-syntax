module Generic.Semantics.Elaboration.LetBinders where

open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function

open import indexed
open import environment
open import Generic.Syntax
open import Generic.Syntax.LetBinders
open import Generic.Semantics
open import Generic.Semantics.Syntactic

module _ {I : Set} {d : Desc I} where

  UnLets : Sem (d `+ Lets) (Tm d _) (Tm d _)
  Sem.th^𝓥  UnLets = th^Tm
  Sem.var   UnLets = id
  Sem.alg   UnLets = case (Sem.alg Substitution) $ λ where
    ((Δ , σ) , est) → case unXs Δ est of λ where
       (es , t , refl) → t $$ es

  unLets : {i : I} → [ Tm (d `+ Lets) _ i ⟶ Tm d _ i ]
  unLets = Sem.sem UnLets (pack `var)

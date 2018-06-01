module Generic.Semantics.Elaboration.LetBinder where

open import Size
open import Data.Product
open import Agda.Builtin.List
open import Function

open import environment
open import Generic.Syntax
open import Generic.Syntax.LetBinder
open import Generic.Semantics

-- Elaborating away a single let-binder. The algebra is defined by case analysis
-- over the constructors:

-- * let-binders are inlined thanks to the substitution _[_/0] which takes two
-- arguments t and e and instatiates the first free variable of t with e.

-- * the other constructors are left as is by reusing Substitution's algebra

module _ {I : Set} where

  UnLet : (d : Desc I) → Sem (d `+ Let) (Tm d ∞) (Tm d ∞)
  Sem.th^𝓥  (UnLet d) = th^Tm
  Sem.var    (UnLet d) = id
  Sem.alg    (UnLet d) = case (Sem.alg Substitution) $ λ where
   (`IN' e t) → let ↑t = reify^Tm (_ ∷ []) t in ↑t [ e /0]

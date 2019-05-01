\begin{code}

{-# OPTIONS --safe --sized-types #-}

module Generic.Syntax.LetCounter where

open import Algebra
open import Data.Bool
open import Data.Product
open import Data.List.All
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Relation.Unary
open import Function

open import Data.Var
open import Generic.Syntax

open import Generic.Syntax.LetBinder using (Let)

data Counter : Set where
  zero : Counter
  one  : Counter
  many : Counter

_+_ : Counter → Counter → Counter
zero + n = n
m + zero = m
_ + _    = many

module _ {I : Set} where

  Count : List I → Set
  Count = All (λ _ → Counter)

  zeros : ∀[ Count ]
  zeros = tabulate (λ _ → zero)

  fromVar : ∀ {i} → ∀[ Var i ⇒ Count ]
  fromVar z     = one ∷ zeros
  fromVar (s v) = zero ∷ fromVar v

  merge : ∀[ Count ⇒ Count ⇒ Count ]
  merge []       []       = []
  merge (m ∷ cs) (n ∷ ds) = m + n ∷ merge cs ds

  rawMonoid : List I → RawMonoid _ _
  rawMonoid Γ = record
    { Carrier = Count Γ
    ; _≈_     = _≡_
    ; _∙_     = merge
    ; ε       = tabulate (λ _ → zero)
    }

module _ {I : Set} where

  CLet : Desc I
  CLet = `σ Counter $ λ _ → Let

pattern `IN' e t = (_ , e , t , refl)
pattern `IN  e t = `con (`IN' e t)

module _ {I : Set} {d : Desc I} where

  embed : ∀ {i σ} → ∀[ Tm d i σ ⇒ Tm (d `+ CLet) i σ ]
  embed = map^Tm (MkDescMorphism (true ,_))

\end{code}

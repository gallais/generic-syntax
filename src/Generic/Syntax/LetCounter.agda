{-# OPTIONS --safe --sized-types #-}

module Generic.Syntax.LetCounter where

open import Algebra
open import Algebra.Structures
open import Data.Bool
open import Data.List.Relation.Unary.All as All
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Relation.Unary
open import Function

open import Data.Var
open import Generic.Syntax

open import Generic.Syntax.LetBinder using (Let)

module _ {a} {A : Set a} (expensive : A) where

-- inlining is hard

  _ : A × A
  -- here we better not inline x (but it's fine to inline y)

  _ =  let x = expensive  in
       let y = (x , x)    in
       y

  _ : A
  -- here on the other hand we can inline all the lets!

  _ =  let x = expensive  in
       let y = (x , x)    in
       x

data Counter : Set where
  zero  : Counter
  one   : Counter
  many  : Counter

_+_ : Counter → Counter → Counter
zero  + n     = n
m     + zero  = m
_     + _     = many

_*_ : Counter → Counter → Counter
zero  * n     = zero
m     * zero  = zero
one   * n     = n
m     * one   = m
many  * many  = many


module _ {I : Set} where

  private
    variable
      σ : I


  Count : List I → Set
  Count = All (const Counter)

  zeros : ∀[ Count ]
  zeros {[]}     = []
  zeros {σ ∷ Γ}  = zero ∷ zeros

  fromVar : ∀[ Var σ ⇒ Count ]
  fromVar z      = one ∷ zeros
  fromVar (s v)  = zero ∷ fromVar v



  merge : ∀[ Count ⇒ Count ⇒ Count ]
  merge []        []        = []
  merge (m ∷ cs)  (n ∷ ds)  =
    (m + n) ∷ merge cs ds



  control : Counter → ∀[ Count ⇒ Count ]
  control zero  cs = zeros
  control one   cs = cs -- inlined
  control many  cs = cs -- not inlined



  scale : Counter → ∀[ Count ⇒ Count ]
  scale zero  cs = zeros
  scale one   cs = cs
  scale k     cs = map (k *_) cs



  rawMonoid : List I → RawMonoid _ _
  rawMonoid Γ = record
    { Carrier = Count Γ
    ; _≈_     = _≡_
    ; _∙_     = merge
    ; ε       = tabulate (λ _ → zero)
    }


  CLet : Desc I
  CLet = `σ Counter $ λ _ → Let



pattern `IN' e t = (_ , e , t , refl)
pattern `IN  e t = `con (`IN' e t)

module _ {I : Set} {d : Desc I} where

  embed : ∀ {i σ} → ∀[ Tm d i σ ⇒ Tm (d `+ CLet) i σ ]
  embed = map^Tm (MkDescMorphism (true ,_))


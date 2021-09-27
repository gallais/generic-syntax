module Stdlib where

open import Data.Product
open import Data.List.Base

private

  variable
    A B : Set

const : Set → (A → Set)
const P x = P

_∙×_ : (P Q : A → Set) → (A → Set)
(P ∙× Q) x = P x × Q x

_⇒_ : (P Q : A → Set) → (A → Set)
(P ⇒ Q) x = P x → Q x

∀[_] : (A → Set) → Set
∀[_] P = ∀ {x} → P x

_⊢_ : (A → B) → (B → Set) → (A → Set)
(f ⊢ P) x = P (f x)




data ⊥ : Set where




data Dec (P : Set) : Set where
  yes  : P        → Dec P
  no   : (P → ⊥)  → Dec P


variable
  a : A
  as : List A


data All (P : A → Set) : List A → Set where
  []   : All P []
  _∷_  : P a → All P as → All P (a ∷ as)

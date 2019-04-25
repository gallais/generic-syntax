module Stdlib where

open import Data.Product

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

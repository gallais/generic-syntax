module Generic.Examples.NbyE where

open import Size
open import Data.Maybe
open import Data.Product
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Function

open import indexed
open import varlike
open import environment
open import Generic.Syntax
open import Generic.Semantics.NbyE

open import Generic.Syntax.UTLC

-- Normalization by Evaluation for the Untyped Lambda Calculus

-- * A Lambda is Already a Value
-- * An Application can behave in two different ways:
--   1. if the function is a lambda then it reduces
--   2. Otherwise the spine of eliminators grows

normUTLC : [ Tm UTLC ∞ _ ⟶ Maybe ∘ Tm UTLC ∞ _ ]
normUTLC = norm $ λ where
  (Lam , b)                       → C (Lam , b)
  (App , C (Lam , b , _) , t , _) → b (base vl^Var) (ε ∙ t)
  (App , ft)                      → C (App , ft)

_ : let open PATTERNS in normUTLC (APP `id (APP `id `id)) ≡ just `id
_ = refl

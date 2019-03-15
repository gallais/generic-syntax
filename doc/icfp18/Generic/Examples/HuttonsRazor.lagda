\begin{code}
module Generic.Examples.HuttonsRazor where

open import Size
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality

open import environment
open import Generic.Syntax
open import Generic.Semantics

-- Hutton's razor as a minimalistic example of a language
-- one may want to evaluate

HuttRaz : Desc ⊤
HuttRaz  =   `σ ℕ (λ _ → `∎ tt)
         `+  `X [] tt (`X [] tt (`∎ tt))

infixr 5 _[+]_
pattern lit n      = `con (true , n , refl)
pattern _[+]_ e f  = `con (false , e , f , refl)

-- Because there are no variables whatsoever in this simple
-- language we can simply associated values of the empty to
-- them. The computation itself will deliver a natural number.

Eval : Sem HuttRaz (λ _ _ → ⊥) (λ _ _ → ℕ)
Sem.th^𝓥  Eval = ⊥-elim
Sem.var   Eval = ⊥-elim
Sem.alg   Eval = case proj₁ (λ { (m , n , _) → m + n })

eval : Tm HuttRaz ∞ tt [] → ℕ
eval = Sem.closed Eval

-- And, sure enough, we are able to run these expressions

3+2 : eval (lit 3 [+] lit 2) ≡ 5
3+2 = refl

[2+6]+0 : eval ((lit 2 [+] lit 6) [+] lit 0) ≡ 8
[2+6]+0 = refl
\end{code}

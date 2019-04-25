{-# OPTIONS --safe --sized-types #-}

module Generic.Examples.Printing where

open import Data.Product
open import Data.String
open import Function
open import Relation.Binary.PropositionalEquality

open import Data.Var
open import Data.Environment
open import Generic.Syntax
open import Generic.Semantics.Printing

-- UTLC
open import Generic.Syntax.UTLC

printLC : Display UTLC
getD printLC = case (λ { (f , t , _)    → f ++ "(" ++ t ++ ")" })
                    (λ { ((x , b) , _)  → "λ" ++ lookup x z ++ ". " ++ b })

open import Agda.Builtin.Equality

_ : print printLC `id ≡ "λa. a"
_ = refl

open import Generic.Examples.HuttonsRazor

open import Data.Nat.Show as Nat

printHR : Display HuttRaz
getD printHR = case (Nat.show ∘ proj₁)
                    (λ { (m , n , _) → m ++ " + " ++ n })

_ : print printHR ((lit 2 [+] lit 6) [+] lit 0) ≡ "2 + 6 + 0"
_ = refl

open import Generic.Examples.SystemF as SystemF

printSF : Display system-F
getD printSF  = case  (λ { (σ , τ , _)    → σ ++ " → " ++ τ })
              $ case  (λ { ((x , b) , _)  → "∀" ++ lookup x z ++ ". " ++ b })
              $ case  (λ { (f , t , _)    → f ++ "(" ++ t ++ ")" })
              $ case  (λ { ((x , b) , _)  → "λ" ++ lookup x z ++ ". " ++ b })
              $ case  (λ { (f , T , _)    → f ++ "(" ++ T ++ ")" })
                      (λ { ((x , b) , _)  → "Λ" ++ lookup x z ++ ". " ++ b })

_ : print printSF SystemF.`id ≡ "Λa. λb. b"
_ = refl

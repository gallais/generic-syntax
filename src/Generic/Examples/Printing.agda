module Generic.Examples.Printing where

open import Data.Nat.Show as Nat
open import Data.String
open import Data.Bool
open import Data.Product
open import Agda.Builtin.Equality
open import Function

open import var
open import environment
open import Generic.Syntax
open import Generic.Semantics.Printing

-- First example: Untyped Lambda Calculus

open import Generic.Syntax.UTLC as UTLC

disUTLC : Display UTLC
getD disUTLC (App  , f , t , _)  = f ++ "(" ++ t ++ ")"
getD disUTLC (Lam , (x , b) , _) = "λ" ++ lookup x z ++ ". " ++ b

_ : print disUTLC UTLC.`id ≡ "λa. a"
_ = refl

-- Second example: Hutton's Razor

open import Generic.Examples.HuttonsRazor

disHR : Display HuttRaz
getD disHR = λ where
  (Lit , n , _)     → Nat.show n
  (Add , m , n , _) → m ++ " + " ++ n

_ : print disHR ((lit 2 [+] lit 6) [+] lit 0) ≡ "2 + 6 + 0"
_ = refl

-- Third example: System F

open import Generic.Examples.SystemF as SystemF

printSF : Display system-F
getD printSF  =
    case  (λ { (σ , τ , _)    → σ ++ " → " ++ τ })
  $ case  (λ { ((x , b) , _)  → "∀" ++ lookup x z ++ ". " ++ b })
  $ case  (λ { (f , t , _)    → f ++ "(" ++ t ++ ")" })
  $ case  (λ { ((x , b) , _)  → "λ" ++ lookup x z ++ ". " ++ b })
  $ case  (λ { (f , T , _)    → f ++ "(" ++ T ++ ")" })
  $       (λ { ((x , b) , _)  → "Λ" ++ lookup x z ++ ". " ++ b })

_ : print printSF SystemF.`id ≡ "Λa. λb. b"
_ = refl

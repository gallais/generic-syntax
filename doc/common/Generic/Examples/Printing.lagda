\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Examples.Printing where

open import Data.Bool
open import Data.Product
open import Data.List.Base using (_∷_; [])
open import Data.String
open import Function
open import Relation.Binary.PropositionalEquality

open import Data.Var
open import Data.Environment
open import StateOfTheArt.ACMM using (module Printer); open Printer
open import Generic.Syntax
open import Generic.Semantics.Printing

-- UTLC
open import Generic.Syntax.UTLC

\end{code}
%<*printUTLC>
\begin{code}
printUTLC : Display UTLC
printUTLC = λ where
  (`app' f t)      → f ++ " (" ++ t ++ ")"
  (`lam' (x , b))  → "λ" ++ getW (lookup x z) ++ ". " ++ b
\end{code}
%</printUTLC>
\begin{code}

open import Agda.Builtin.Equality

\end{code}
%<*printid>
\begin{code}
_ : print printUTLC id^U ≡ "λa. a"
_ = refl
\end{code}
%</printid>
%<*printopen>
\begin{code}
_ : let tm : Tm UTLC _ _ (_ ∷ _ ∷ [])
        tm = `app (`var z) (`lam (`var (s (s z))))
    in print printUTLC tm ≡ "b (λc. a)"
_ = refl
\end{code}
%</printopen>
\begin{code}

open import Generic.Examples.HuttonsRazor

open import Data.Nat.Show as Nat

printHR : Display HuttRaz
printHR = λ where
  (true , n , _)      → Nat.show n
  (false , m , n , _) → m ++ " + " ++ n

_ : let expr : TM HuttRaz _ ;expr = ((lit 2 [+] lit 6) [+] lit 0)
    in print printHR expr ≡ "2 + 6 + 0"
_ = refl

open import Generic.Examples.SystemF as SystemF

printSF : Display system-F
printSF  = case  (λ { (σ , τ , _)    → σ ++ " → " ++ τ })
         $ case  (λ { ((x , b) , _)  → "∀" ++ getW (lookup x z) ++ ". " ++ b })
         $ case  (λ { (f , t , _)    → f ++ "(" ++ t ++ ")" })
         $ case  (λ { ((x , b) , _)  → "λ" ++ getW (lookup x z) ++ ". " ++ b })
         $ case  (λ { (f , T , _)    → f ++ "(" ++ T ++ ")" })
                      (λ { ((x , b) , _)  → "Λ" ++ getW (lookup x z) ++ ". " ++ b })

_ : print printSF SystemF.`id ≡ "Λa. λb. b"
_ = refl
\end{code}

\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Syntax.UTLC where

open import Size
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.List.Base hiding ([_])
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Var
open import Generic.Syntax

\end{code}
%<*ULC>
\begin{code}
UTLC : Desc ⊤
UTLC = `σ Bool $ λ isApp → if isApp
  then  `X [] tt (`X [] tt (`∎ tt))
  else  `X (tt ∷ []) tt (`∎ tt)
\end{code}
%</ULC>
\begin{code}
private
  module DISPLAYONLY where
\end{code}
%<*LCpat>
\begin{code}
    pattern `app f t  = `con (true , f , t , refl)
    pattern `lam b    = `con (false , b , refl)
\end{code}
%</LCpat>
\begin{code}
pattern `app' f t  = (true , f , t , refl)
pattern `lam' b    = (false , b , refl)
pattern `app  f t  = `con (`app' f t)
pattern `lam  b    = `con (`lam' b)
\end{code}
%<*LCid>
\begin{code}
id^U : Tm UTLC ∞ tt []
id^U = `lam (`var z)
\end{code}
%</LCid>

\begin{code}
module Generic.Examples.UntypedLC where

open import Size
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.List.Base hiding ([_])
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import indexed
open import var
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
%<*LCpat>
\begin{code}
pattern `V x    = `var x
pattern `A f t  = `con (true , f , t , refl)
pattern `L b    = `con (false , b , refl)
\end{code}
%</LCpat>
%<*LCid>
\begin{code}
`id : Tm UTLC ∞ tt []
`id = `L (`V z)
\end{code}
%</LCid>

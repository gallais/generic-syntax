\begin{code}
module Generic.Examples.STLC where

open import Data.Bool
open import Agda.Builtin.List
open import Generic.Syntax
open import motivation using (Type ; _⇒_)
open import Function
\end{code}
%<*stlc>
\begin{code}
STLC : Desc Type
STLC =  `σ Bool $ λ isApp → if isApp
        then  (`σ Type $ λ σ →
              `σ Type $ λ τ →
              `X [] (σ ⇒ τ) (`X [] σ (`∎ τ)))
        else  (`σ Type $ λ σ →
              `σ Type $ λ τ →
              `X (σ ∷ []) τ (`∎ (σ ⇒ τ)))
\end{code}
%</stlc>

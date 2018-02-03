\begin{code}
module Generic.Examples.STLC where

open import Size
open import Data.Bool
open import Data.Product
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Generic.Syntax
open import var
open import motivation using (Type ; α ; _⇒_)
open import Function
\end{code}
%<*stlc>
\begin{code}
data `STLC : Set where
  App Lam : Type → Type → `STLC

STLC : Desc Type
STLC =  `σ `STLC $ λ where
  (App σ τ) → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ))
  (Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ ⇒ τ))
\end{code}
%</stlc>
%<*patST>
\begin{code}
pattern `V x    = `var x
pattern `A f t  = `con (App _ _ , f , t , refl)
pattern `L b    = `con (Lam _ _ , b , refl)
\end{code}
%</patST>
\begin{code}
_ : Tm STLC ∞ ((α ⇒ α) ⇒ (α ⇒ α)) []
_ = `L (`L (`A (`V (s z)) (`V z)))
\end{code}

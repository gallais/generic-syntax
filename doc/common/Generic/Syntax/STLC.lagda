\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Syntax.STLC where

open import Size
open import Data.Bool
open import Data.Product
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Generic.Syntax
open import Data.Var
open import StateOfTheArt.ACMM using (Type ; α ; _`→_)
open import Function

private
  variable
    σ : Type

\end{code}
%<*stlc>
\begin{AgdaAlign}
%<*tag>
\begin{code}
data `STLC : Set where
  App Lam : Type → Type → `STLC
\end{code}
%</tag>
\begin{AgdaSuppressSpace}
%<*desc>
\begin{code}
STLC : Desc Type
STLC = `σ `STLC $ λ where
  (App σ τ) → `X [] (σ `→ τ) (`X [] σ (`∎ τ))
  (Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ `→ τ))
\end{code}
%</desc>
\end{AgdaSuppressSpace}
\end{AgdaAlign}
%</stlc>
%<*patST>
\begin{code}
pattern `app f t  = `con (App _ _ , f , t , refl)
pattern `lam b    = `con (Lam _ _ , b , refl)
\end{code}
%</patST>
\begin{code}
_ : Tm STLC ∞ ((α `→ α) `→ (α `→ α)) []
_ = `lam (`lam (`app (`var (s z)) (`var z)))
\end{code}

%<*STid>
\begin{code}
id^S : Tm STLC ∞ (σ `→ σ) []
id^S = `lam (`var z)
\end{code}
%</STid>

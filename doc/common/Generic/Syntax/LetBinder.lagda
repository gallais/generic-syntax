\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Syntax.LetBinder where

open import Size
open import Data.Bool
open import Data.Product
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Function
open import Relation.Unary

open import Generic.Syntax

private
  variable
    I : Set
    σ τ : I
    d : Desc I
    s : Size


module _ {I : Set} where

\end{code}
%<*letcode>
\begin{code}
  Let : Desc I
  Let = `σ (I × I) $ uncurry $ λ σ τ →
        `X [] σ (`X (σ ∷ []) τ (`∎ τ))
\end{code}
%</letcode>
%<*letpattern>
\begin{code}
pattern `let'_`in'_  e t = (_ , e , t , refl)
pattern `let_`in_    e t = `con (`let' e `in' t)
\end{code}
%</letpattern>

\begin{code}
embed : ∀[ Tm d s σ ⇒ Tm (d `+ Let) s σ ]
embed = map^Tm (MkDescMorphism (true ,_))
\end{code}

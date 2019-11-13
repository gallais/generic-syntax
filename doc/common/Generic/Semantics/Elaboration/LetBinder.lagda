\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Semantics.Elaboration.LetBinder where

open import Size
open import Data.Product
open import Agda.Builtin.List
open import Function
open import Relation.Unary

open import Data.Environment
open import Generic.Syntax
open import Generic.Syntax.LetBinder
open import Generic.Semantics
open import Generic.Semantics.Syntactic

private
  variable
    I : Set
    d : Desc I
    σ : I
    Γ Δ : List I
    s : Size

-- Elaborating away a single let-binder. The algebra is defined by case analysis
-- over the constructors:

-- * let-binders are inlined thanks to the substitution _[_/0] which takes two
-- arguments t and e and instatiates the first free variable of t with e.

-- * the other constructors are left as is by reusing Substitution's algebra


\end{code}
%<*unletcode>
\begin{code}
UnLet : Semantics (d `+ Let) (Tm d ∞) (Tm d ∞)
Semantics.th^𝓥  UnLet = th^Tm
Semantics.var   UnLet = id
Semantics.alg   UnLet = case (Semantics.alg Sub) $ λ where
 (`let' e `in' t) →  extract t (ε ∙ e)
\end{code}
%</unletcode>
\begin{code}

unLet : (Γ ─Env) (Tm d ∞) Δ → Tm (d `+ Let) s σ Γ → Tm d ∞ σ Δ
unLet ρ t = Semantics.semantics UnLet ρ t

\end{code}
%<*unlet>
\begin{code}
unlet : ∀[ Tm (d `+ Let) ∞ σ ⇒ Tm d ∞ σ ]
unlet = Semantics.semantics UnLet id^Tm 
\end{code}
%</unlet>

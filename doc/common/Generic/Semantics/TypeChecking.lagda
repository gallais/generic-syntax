\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Semantics.TypeChecking where

open import Size
open import Function
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.List hiding ([_])
open import Data.Maybe
import Data.Maybe.Categorical as MC

open import Data.Var hiding (_<$>_)
open import Data.Environment hiding (_<$>_ ; _>>_)
open import Generic.Syntax
open import Generic.Syntax.Bidirectional; open PATTERNS
open import Generic.Semantics

import Category.Monad as CM
import Level
module M = CM.RawMonad (MC.monad {Level.zero})
open M

open import Relation.Binary.PropositionalEquality hiding ([_])

infix 2 _==_
\end{code}
%<*typeeq>
\begin{code}
_==_ : (σ τ : Type) → Maybe ⊤
α           == α            = just tt
(σ₁ `→ τ₁)  == (σ₂ `→ τ₂)   = (σ₁ == σ₂) >> (τ₁ == τ₂)
_           == _            = nothing
\end{code}
%</typeeq>
%<*isArrow>
\begin{code}
isArrow : (σ : Type) → Maybe (Type × Type)
isArrow (σ `→ τ) = just (σ , τ)
isArrow _       = nothing
\end{code}
%</isArrow>

\begin{code}

private
  variable
    i : Mode
    Γ : List Mode

\end{code}

%<*typemode>
\begin{code}
Type- : Mode → Set
Type- Check  = Type →  Maybe ⊤
Type- Infer  =         Maybe Type
\end{code}
%</typemode>
%<*varmode>
\begin{code}
data Var- : Mode → Set where
  `var : Type → Var- Infer
\end{code}
%</varmode>

%<*app>
\begin{code}
app : Type- Infer → Type- Check → Type- Infer
app f t = do
  arr      ← f
  (σ , τ)  ← isArrow arr
  τ <$ t σ
\end{code}
%</app>
%<*cut>
\begin{code}
cut : Type → Type- Check → Type- Infer
cut σ t = σ <$ t σ
\end{code}
%</cut>
%<*emb>
\begin{code}
emb : Type- Infer → Type- Check
emb t σ = do
  τ ← t
  σ == τ
\end{code}
%</emb>
%<*lam>
\begin{code}
lam : Kripke (const ∘ Var-) (const ∘ Type-) (Infer ∷ []) Check Γ → Type- Check
lam b arr = do
  (σ , τ) ← isArrow arr
  b (bind Infer) (ε ∙ `var σ) τ
\end{code}
%</lam>

%<*typecheck>
\begin{code}
Typecheck : Semantics Bidi (const ∘ Var-) (const ∘ Type-)
Semantics.th^𝓥  Typecheck = th^const
Semantics.var   Typecheck = λ where (`var σ) → just σ
Semantics.alg   Typecheck = λ where
  (`app' f t)  → app f t
  (`cut' σ t)  → cut σ t
  (`emb' t)    → emb t
  (`lam' b)    → lam b
\end{code}
%</typecheck>

%<*type->
\begin{code}
type- : (p : Mode) → TM Bidi p → Type- p
type- p t = Semantics.closed Typecheck t
\end{code}
%</type->
%<*example>
\begin{code}
_ : let  id  : Tm Bidi ∞ Check []
         id  = `lam (`emb (`var z))
    in type- Infer (`app (`cut ((α `→ α) `→ (α `→ α)) id) id)
     ≡ just (α `→ α)
_ = refl
\end{code}
%</example>

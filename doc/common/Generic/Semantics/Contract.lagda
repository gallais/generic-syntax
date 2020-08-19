\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Semantics.Contract where

open import Size
open import Data.List hiding ([_] ; lookup)
open import Data.Maybe as Maybe
open import Data.Maybe.Categorical
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Relation.Unary
open import Data.Var
open import Data.Var.Varlike
open import Data.Environment
open import Data.Relation
open import Generic.Syntax
open import Generic.Semantics

open Semantics

private
  variable
    I : Set
    σ τ : I
    Γ Δ : List I
    d : Desc I

MVar : I ─Scoped
MVar i Γ = Maybe (Var i Γ)

th^MVar : Thinnable (MVar σ)
th^MVar mv ρ = Maybe.map (λ v → th^Var v ρ) mv

vl^MVar : VarLike {I} MVar
th^𝓥 vl^MVar = th^MVar
new vl^MVar = just z

MTm : ∀ d → I ─Scoped
MTm d i Γ = Maybe (Tm d _ i Γ)

\end{code}
%<*contractsem>
\begin{code}
Contract : Semantics d MVar (MTm d)
th^𝓥 Contract = th^MVar
var Contract = Maybe.map `var
alg Contract = Maybe.map `con ∘ mapA _ (reify vl^MVar)
  where instance _ = applicative
\end{code}
%</contractsem>

%<*contract>
\begin{code}
contract : Tm d _ σ (τ ∷ Γ) → Maybe (Tm d _ σ Γ)
contract = semantics Contract (pack just ∙ nothing)
\end{code}
%</contract>

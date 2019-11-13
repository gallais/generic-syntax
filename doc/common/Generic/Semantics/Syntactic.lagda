\begin{code}
{-# OPTIONS --safe --sized-types #-}

open import Generic.Syntax using (Desc)

module Generic.Semantics.Syntactic {I} {d : Desc I} where

open import Size
open import Data.List hiding ([_] ; lookup)
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
    σ τ : I
    Γ Δ : List I

\end{code}
%<*renaming>
\begin{code}
Ren : Semantics d Var (Tm d ∞)
Ren .th^𝓥  = th^Var
Ren .var   = `var
Ren .alg   = `con ∘ fmap d (reify vl^Var)
\end{code}
%</renaming>
%<*thTm>
\begin{code}
th^Tm : Thinnable (Tm d ∞ σ)
th^Tm t ρ = Semantics.semantics Ren ρ t
\end{code}
%</thTm>
\begin{code}

vl^Tm : VarLike (Tm d ∞)
new   vl^Tm = `var z
th^𝓥  vl^Tm = th^Tm
\end{code}
%<*substitution>
\begin{code}
Sub : Semantics d (Tm d ∞) (Tm d ∞)
Sub .th^𝓥  = th^Tm
Sub .var   = id
Sub .alg   = `con ∘ fmap d (reify vl^Tm)
\end{code}
%</substitution>
\begin{code}
module PAPERONLY where
\end{code}
%<*ren>
\begin{code}
 ren : (Γ ─Env) Var Δ →
       Tm d ∞ σ Γ → Tm d ∞ σ Δ
 ren ρ t = Semantics.semantics Ren ρ t
\end{code}
%</ren>
%<*sub>
\begin{code}
 sub : (Γ ─Env) (Tm d ∞) Δ →
       Tm d ∞ σ Γ → Tm d ∞ σ Δ
 sub ρ t = Semantics.semantics Sub ρ t
\end{code}
%</sub>
\begin{code}
ren : Thinning Γ Δ → (Γ ─Comp) (Tm d ∞) Δ
ren = Semantics.semantics Ren

sub : ∀ {s} → (Γ ─Env) (Tm d ∞) Δ → Tm d s σ Γ → Tm d ∞ σ Δ
sub ρ t = Semantics.semantics Sub ρ t

vl^VarTm : VarLikeᴿ VarTmᴿ vl^Var vl^Tm
VarLikeᴿ.newᴿ  vl^VarTm = refl
VarLikeᴿ.thᴿ   vl^VarTm = λ σ → cong (ren σ)

reify^Tm : ∀ Δ → ∀[ Kripke (Tm d ∞) (Tm d ∞) Δ σ ⇒ (Δ ++_) ⊢ Tm d ∞ σ ]
reify^Tm Δ = reify vl^Tm Δ _

id^Tm : (Γ ─Env) (Tm d ∞) Γ
lookup id^Tm = `var

lookup-base^Tm : (k : Var σ Γ) → lookup (base vl^Tm) k ≡ `var k
lookup-base^Tm z                              = refl
lookup-base^Tm (s k) rewrite lookup-base^Tm k = refl

base^VarTmᴿ : ∀ {Γ} → All VarTmᴿ Γ (base vl^Var) (base vl^Tm)
lookupᴿ base^VarTmᴿ k = begin
  `var (lookup (base vl^Var) k) ≡⟨ cong `var (lookup-base^Var k) ⟩
  `var k                        ≡⟨ sym (lookup-base^Tm k) ⟩
  lookup (base vl^Tm) k ∎

infix 5 _[_
infix 6 _/0]

_/0] : Tm d ∞ σ Γ → (σ ∷ Γ ─Env) (Tm d ∞) Γ
_/0] = singleton vl^Tm

_[_ : Tm d ∞ τ (σ ∷ Γ) → (σ ∷ Γ ─Env) (Tm d ∞) Γ → Tm d ∞ τ Γ
t [ ρ = sub ρ t
\end{code}

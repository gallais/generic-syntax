\begin{code}
{-# OPTIONS --safe --sized-types #-}

open import Generic.Syntax

module Generic.Semantics.Elaboration.LetCounter {I : Set} {d : Desc I} where

import Level as L
open import Size
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Data.Product
import Data.Product.Categorical.Right as PC
open import Data.List.Base
open import Data.List.Relation.Unary.All as All using (All; _∷_)
open import Data.List.Relation.Unary.All.Properties
open import Function

open import Data.Var
open import Data.Var.Varlike
open import Data.Environment using (Kripke; th^Var; ε; _∙_; extend)
open import Generic.Syntax.LetCounter
open import Generic.Syntax.LetBinder
open import Generic.Semantics
open import Generic.Semantics.Syntactic

private
  variable
    Γ Δ : List I
    σ : I

module PCR {Γ : List I} = PC L.zero (rawMonoid Γ)
instance _ = PCR.applicative

\end{code}
%<*counted>
\begin{code}
Counted : I ─Scoped → I ─Scoped
Counted T i Γ = T i Γ × Count Γ
\end{code}
%</counted>
%<*reifycount>
\begin{code}
reify^Count :  ∀ Δ σ →
  Kripke Var (Counted (Tm (d `+ CLet) ∞)) Δ σ Γ →
  Counted (Scope (Tm (d `+ CLet) ∞) Δ) σ Γ
reify^Count Δ σ kr =  let (scp , c) = reify vl^Var Δ σ kr in
                      scp , ++⁻ʳ Δ c
\end{code}
%</reifycount>
%<*letcount>
\begin{code}
letcount : ⟦ Let ⟧ (Kripke Var (Counted (Tm (d `+ CLet) ∞))) σ Γ →
           Counted (⟦ CLet ⟧ (Scope (Tm (d `+ CLet) ∞))) σ Γ
letcount (στ , (e , ce) , tct , eq) = case tct extend (ε ∙ z) of λ where
  (t , cx ∷ ct) →  (cx , στ , e , t , eq) , merge (scale cx ce) ct
\end{code}
%</letcount>

\begin{code}
LetCount : Semantics (d `+ Let) Var (Counted (Tm (d `+ CLet) ∞))
Semantics.th^𝓥  LetCount = th^Var
Semantics.var    LetCount = λ v → `var v , fromVar v
Semantics.alg    LetCount = λ where
  (true , t)    → let (t' , c)   = mapA d reify^Count t in `con (true , t') , c
  (false , et)  → let (et' , c)  = letcount et in `con (false , et') , c
\end{code}
%<*annotatetype>
\begin{code}
annotate : Tm (d `+ Let) ∞ σ Γ → Tm (d `+ CLet) ∞ σ Γ
\end{code}
%</annotatetype>
\begin{code}
annotate = proj₁ ∘′ Semantics.semantics LetCount (base vl^Var)

Inline : Semantics (d `+ CLet) (Tm (d `+ Let) ∞) (Tm (d `+ Let) ∞)
Semantics.th^𝓥 Inline = th^Tm
Semantics.var   Inline = id
Semantics.alg   Inline = λ where
  (true , t)                       → `con (true , fmap d (reify vl^Tm) t)
  (false , many , στ , e , b , eq) → `con (false , στ , e , b extend (ε ∙ `var z) , eq)
  (false , _ , στ , e , b , refl)  → b (base vl^Var) (ε ∙ e)

inline : Tm (d `+ CLet) ∞ σ Γ → Tm (d `+ Let) ∞ σ Γ
inline = Semantics.semantics Inline (base vl^Tm)

inline-affine : Tm (d `+ Let) ∞ σ Γ → Tm (d `+ Let) ∞ σ Γ
inline-affine = inline ∘′ annotate
\end{code}

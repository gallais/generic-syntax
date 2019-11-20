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
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; _∷_)
open import Data.List.Relation.Unary.All.Properties renaming (++⁻ʳ to drop)
open import Function

open import Relation.Unary
open import Data.Var
open import Data.Var.Varlike
open import Data.Environment using (Kripke; th^Var; ε; _∙_; identity; extend; extract)
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
reify^Count : ∀ Δ σ →  Kripke Var (Counted (Tm (d `+ CLet) ∞)) Δ σ Γ →
                       Counted (Scope (Tm (d `+ CLet) ∞) Δ) σ Γ
reify^Count Δ σ kr = let (scp , c) = reify vl^Var Δ σ kr in scp , drop Δ c
\end{code}
%</reifycount>
%<*letcount>
\begin{code}
clet :  ⟦ Let ⟧ (Kripke Var (Counted (Tm (d `+ CLet) ∞))) σ Γ →
        Counted (⟦ CLet ⟧ (Scope (Tm (d `+ CLet) ∞))) σ Γ
clet (στ , (e , ce) , body , eq) = case body extend (ε ∙ z) of λ where
  (t , cx ∷ ct) →  (cx , στ , e , t , eq) , merge (control cx ce) ct
\end{code}
%</letcount>

%<*Annotate>
\begin{code}
Annotate : Semantics (d `+ Let) Var (Counted (Tm (d `+ CLet) ∞))
Semantics.th^𝓥   Annotate = th^Var
Semantics.var    Annotate = λ v → `var v , fromVar v
Semantics.alg    Annotate = λ where
  (true , t)    → let (t' , c)   = mapA d reify^Count t in `con (true , t') , c
  (false , et)  → let (et' , c)  = clet et in `con (false , et') , c
\end{code}
%</Annotate>

%<*annotate>
\begin{AgdaAlign}
\begin{AgdaSuppressSpace}
%<*annotatetype>
\begin{code}
annotate : ∀[ Tm (d `+ Let) ∞ σ ⇒ Tm (d `+ CLet) ∞ σ ]
\end{code}
%</annotatetype>
\begin{code}
annotate t = let (t' , _) = Semantics.semantics Annotate identity t in t'
\end{code}
\end{AgdaSuppressSpace}
\end{AgdaAlign}
%</annotate>
\begin{code}

Inline : Semantics (d `+ CLet) (Tm (d `+ Let) ∞) (Tm (d `+ Let) ∞)
Semantics.th^𝓥 Inline = th^Tm
Semantics.var   Inline = id
Semantics.alg   Inline = λ where
  (true , t)                       → `con (true , fmap d (reify vl^Tm) t)
  (false , many , στ , e , b , eq) → `con (false , στ , e , b extend (ε ∙ `var z) , eq)
  (false , _ , στ , e , b , refl)  → extract b (ε ∙ e) -- cf Semantics.alg UnLet

inline : Tm (d `+ CLet) ∞ σ Γ → Tm (d `+ Let) ∞ σ Γ
inline = Semantics.semantics Inline id^Tm 

inline-affine : Tm (d `+ Let) ∞ σ Γ → Tm (d `+ Let) ∞ σ Γ
inline-affine = inline ∘′ annotate
\end{code}

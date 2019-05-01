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
open import Data.List.Relation.Unary.All as All using (All)
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

Counted : I ─Scoped → I ─Scoped
Counted T i Γ = T i Γ × Count Γ

reify^Count :  ∀ Δ σ →
  Kripke Var (Counted (Tm (d `+ CLet) ∞)) Δ σ Γ →
  Counted (Scope (Tm (d `+ CLet) ∞) Δ) σ Γ
reify^Count Δ σ kr =  let (scp , c) = reify vl^Var Δ σ kr in
                      scp , ++⁻ʳ Δ c

LetCount : Semantics (d `+ Let) Var (Counted (Tm (d `+ CLet) ∞))
Semantics.th^𝓥  LetCount = th^Var
Semantics.var    LetCount = λ v → `var v , fromVar v
Semantics.alg    LetCount = λ where
  (true , t) → map₁ (`con ∘′ (true ,_)) (mapA d reify^Count t)
  (false , στ , (e , ce) , tct , refl) →
    let (t , ct) = tct extend (ε ∙ z)
        e-usage  = All.head ct
    in `con (false , e-usage , στ , e , t , refl)
     , -- if e (the let-bound expression) is not used in t (the body of the let)
       -- we can ignore its contribution to the count:
       (case e-usage of λ where
         zero → All.tail ct
         _    → merge ce (All.tail ct))

annotate : Tm (d `+ Let) ∞ σ Γ → Tm (d `+ CLet) ∞ σ Γ
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

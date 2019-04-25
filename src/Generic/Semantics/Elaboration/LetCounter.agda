{-# OPTIONS --safe --sized-types #-}

module Generic.Semantics.Elaboration.LetCounter where

import Level as L
open import Size
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Data.Product
import Data.Product.Categorical.Right as PC
open import Data.List.Base
open import Data.List.All as All
open import Data.List.All.Properties
open import Function

open import Data.Var
open import Data.Var.Varlike
open import Data.Environment using (Kripke; th^Var; ε; _∙_; extend)
open import Generic.Syntax
import Generic.Syntax.LetCounter as LetCounter
open LetCounter hiding (Let)
import Generic.Syntax.LetBinder as LetBinder
open import Generic.Semantics
open import Generic.Semantics.Syntactic

module _ {I : Set} {d : Desc I} where

  module PCR {Γ : List I} = PC L.zero (rawMonoid Γ)

  Counted : I ─Scoped → I ─Scoped
  Counted T i Γ = T i Γ × Count Γ

  count : ∀ {σ Γ} e → ⟦ e ⟧ (Kripke Var (Counted (Tm (d `+ LetCounter.Let) ∞))) σ Γ →
                      Counted (⟦ e ⟧ (Scope (Tm (d `+ LetCounter.Let) ∞))) σ Γ
  count (`σ A e)   (a , t)  = map₁ (a ,_) (count (e a) t)
  count (`X Δ j e) (kr , t) =
    let (r , cr) = reify vl^Var Δ j kr
        (u , cu) = count e t
    in (r , u) , merge (++⁻ʳ Δ cr) cu
  count (`∎ eq)    t        = t , zeros

  LetCount : Semantics (d `+ LetBinder.Let) Var (Counted (Tm (d `+ LetCounter.Let) ∞))
  Semantics.th^𝓥  LetCount = th^Var
  Semantics.var    LetCount = λ v → `var v , fromVar v
  Semantics.alg    LetCount = λ where
    (true , t) → map₁ (`con ∘′ (true ,_)) (count d t)
    (false , στ , (e , ce) , tct , refl) →
      let (t , ct) = tct extend (ε ∙ z)
          e-usage  = All.head ct
      in `con (false , e-usage , στ , e , t , refl)
       , -- if e (the let-bound expression) is not used in t (the body of the let)
         -- we can ignore its contribution to the count:
         (case e-usage of λ where
           zero → All.tail ct
           _    → merge ce (All.tail ct))

  annotate : ∀ {σ Γ} → Tm (d `+ LetBinder.Let) ∞ σ Γ → Tm (d `+ LetCounter.Let) ∞ σ Γ
  annotate = proj₁ ∘′ Semantics.semantics LetCount (base vl^Var)

  Inline : Semantics (d `+ LetCounter.Let) (Tm (d `+ LetBinder.Let) ∞)
                                     (Tm (d `+ LetBinder.Let) ∞)
  Semantics.th^𝓥 Inline = th^Tm
  Semantics.var   Inline = id
  Semantics.alg   Inline = λ where
    (true , t)                       → `con (true , fmap d (reify vl^Tm) t)
    (false , many , στ , e , b , eq) → `con (false , στ , e , b extend (ε ∙ `var z) , eq)
    (false , _ , στ , e , b , refl)  → b (base vl^Var) (ε ∙ e)

  inline : ∀ {σ Γ} → Tm (d `+ LetCounter.Let) ∞ σ Γ → Tm (d `+ LetBinder.Let) ∞ σ Γ
  inline = Semantics.semantics Inline (base vl^Tm)

  inline-affine : ∀ {σ Γ} → Tm (d `+ LetBinder.Let) ∞ σ Γ → Tm (d `+ LetBinder.Let) ∞ σ Γ
  inline-affine = inline ∘′ annotate

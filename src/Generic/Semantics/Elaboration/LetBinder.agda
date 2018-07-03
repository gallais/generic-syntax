module Generic.Semantics.Elaboration.LetBinder where

open import Size
open import Data.Product
open import Agda.Builtin.List
open import Function

open import indexed
open import environment
open import Generic.Syntax
open import Generic.Syntax.LetBinder
open import Generic.Semantics

-- Elaborating away a single let-binder. The algebra is defined by case analysis
-- over the constructors:

-- * let-binders are inlined thanks to the substitution _[_/0] which takes two
-- arguments t and e and instatiates the first free variable of t with e.

-- * the other constructors are left as is by reusing Substitution's algebra

module _ {I : Set} {d : Desc I} where

  UnLet : Sem (d `+ Let) (Tm d ∞) (Tm d ∞)
  Sem.th^𝓥  UnLet = th^Tm
  Sem.var    UnLet = id
  Sem.alg    UnLet = case (Sem.alg Substitution) $ λ where
   (`IN' e t) →  extract t (ε ∙ e)

  unLet : ∀{Γ Δ σ s} → (Γ ─Env) (Tm d ∞) Δ → Tm (d `+ Let) s σ Γ → Tm d ∞ σ Δ
  unLet ρ t = Sem.sem UnLet ρ t

  unlet : {i : I} → [ Tm (d `+ Let) ∞ i ⟶ Tm d ∞ i ]
  unlet = Sem.sem UnLet (pack `var)


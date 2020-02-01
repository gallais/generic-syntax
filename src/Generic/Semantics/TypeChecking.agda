{-# OPTIONS --safe --sized-types #-}

module Generic.Semantics.TypeChecking where

open import Size
open import Function
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Data.List hiding ([_])
open import Data.Maybe using (Maybe; nothing; just)
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

infix 2 _=?_

_=?_ : (σ τ : Type) → Maybe ⊤
α         =? α         = just tt
(σ `→ τ)  =? (φ `→ ψ)  = (σ =? φ) >> (τ =? ψ)
_         =? _         = nothing

isArrow : Type → Maybe (Type × Type)
isArrow (σ `→ τ)  = just (σ , τ)
isArrow _         = nothing


private
  variable
    i : Mode
    Γ : List Mode


Type- : Mode → Set
Type- Check  = Type →  Maybe ⊤
Type- Infer  =         Maybe Type

data Var- : Mode → Set where
  `var : Type → Var- Infer

app : Type- Infer → Type- Check → Type- Infer
app f t = do
  arr      ← f
  (σ , τ)  ← isArrow arr
  τ <$ t σ

cut : Type → Type- Check → Type- Infer
cut σ t = σ <$ t σ

emb : Type- Infer → Type- Check
emb t σ = do
  τ ← t
  σ =? τ

lam : Kripke (const ∘ Var-) (const ∘ Type-) (Infer ∷ []) Check Γ → Type- Check
lam b arr = do
  (σ , τ) ← isArrow arr
  b (bind Infer) (ε ∙ `var σ) τ

Typecheck : Semantics Bidi (const ∘ Var-) (const ∘ Type-)
Semantics.th^𝓥  Typecheck = th^const
Semantics.var   Typecheck = λ where (`var σ) → just σ
Semantics.alg   Typecheck = λ where
  (`app' f t)  → app f t
  (`cut' σ t)  → cut σ t
  (`emb' t)    → emb t
  (`lam' b)    → lam b

type- : ∀ p → TM Bidi p → Type- p
type- p = Semantics.closed Typecheck

module _ where

  private β = α `→ α


  _ : type- Infer (`app (`cut (β `→ β) id^B) id^B) ≡ just β
  _ = refl

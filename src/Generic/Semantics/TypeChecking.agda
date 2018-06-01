module Generic.Semantics.TypeChecking where


open import Function
open import Data.Unit
open import Data.Bool
open import Data.Product as P hiding (,_)
open import Data.List hiding ([_])
open import Data.Maybe as Maybe hiding (All)

open import indexed
open import var hiding (_<$>_)
open import environment hiding (_<$>_ ; _>>_)
open import Generic.Syntax
open import Generic.Semantics

import Category.Monad as CM
import Level
module M = CM.RawMonad (Maybe.monad {Level.zero})
open M

open import Relation.Binary.PropositionalEquality hiding ([_])

-- Types and equality testing
infixr 5 _⇒_
data Type : Set where
  α    : Type
  _⇒_  : Type → Type → Type

infix 3 _==_
_==_ : (σ τ : Type) → Maybe ⊤
α     == α       = just tt
σ ⇒ τ == σ' ⇒ τ' = (σ == σ') >> (τ == τ')
_     == _       = nothing

-- Trying to break down a putative arrow type into its constituents
isArrow : (σ⇒τ : Type) → Maybe (Type × Type)
isArrow (σ ⇒ τ) = just (σ , τ)
isArrow _       = nothing

----------------------------------------------------------------------
-- Language Definition

-- We have an *untyped* language presented in a bidirectional manner
-- where phases are statically checked

data `Lang : Set where
  App Lam Emb : `Lang
  Cut : Type → `Lang

data Phase : Set where
  Check Infer : Phase

-- On top of the traditional Application and Lambda-Abstraction constructors,
-- we have two change of direction ones: `Emb` which takes inferable terms and
-- makes them checkable (it is enough to compare the inferred type to the
-- candidate provided); and `Cut` which takes a checkable term and makes it
-- inferrable thanks to a type-annotation.

Lang : Desc Phase
Lang  =  `σ `Lang $ λ where
  App      → `X [] Infer (`X [] Check (`∎ Infer))
  Lam      → `X (Infer ∷ []) Check (`∎ Check)
  (Cut σ)  → `X [] Check (`∎ Infer)
  Emb      → `X [] Infer (`∎ Check)

pattern APP f t  = `con (App , f , t , refl)
pattern LAM b    = `con (Lam , b , refl)
pattern CUT σ t  = `con (Cut σ , t , refl)
pattern EMB t    = `con (Emb , t , refl)

----------------------------------------------------------------------
-- Type- Checking/Inference

-- The output of the semantics is the Type-(Check/Infer) process itself.
-- Hence the following definition

Type- : Phase → Set
Type- Check  = Type →  Maybe ⊤
Type- Infer  =         Maybe Type

Var- : Phase → Set
Var- _ = Type

Typecheck : Sem Lang (const ∘ Var-) (const ∘ Type-)
Typecheck = record { th^𝓥 = λ v ρ → v; var = var _; alg = alg } where

   var : (i : Phase) → Var- i → Type- i
   var Infer  = just
   var Check  = _==_

   alg : {i : Phase} {Γ : List Phase} →
         ⟦ Lang ⟧ (Kripke (κ ∘ Var-) (κ ∘ Type-)) i Γ → Type- i
   -- Application:
   --  * Infer the type of the function
   --  * Make sure it is an arrow type
   --  * Check the argument belongs to the domain
   --  * Return the codomain
   alg (App , f , t , refl)  =  f            >>= λ σ⇒τ →
                                isArrow σ⇒τ  >>= uncurry λ σ τ →
                                τ <$ t σ
   -- Lambda-Abstraction:
   --  * Make sure the candidate is an arrow type
   --  * Push a fresh variable of type the domain in the context
   --  * Check the body has type the codomain in the extended context
   alg (Lam , b , refl)      =  λ σ⇒τ → isArrow σ⇒τ >>= uncurry λ σ τ →
                                b (extend {σ = Infer}) (ε ∙ σ) τ
   -- Cut aka Type Annotation:
   --  * Check the term as the ascribed type
   --  * Return that type
   alg (Cut σ , t , refl)    =  σ <$ t σ
   -- Embedding:
   --  * Infer the type of the term
   --  * Check it is equal to the candidate
   alg (Emb , t , refl)      =  λ σ → t >>= λ τ → σ == τ

type- : (p : Phase) → TM Lang p → Type- p
type- p t = Sem.sem Typecheck {Δ = []} ε t

----------------------------------------------------------------------
-- Example

_ : let  id  : TM Lang Check
         id  = LAM (EMB (`var z))
    in type- Infer (APP (CUT ((α ⇒ α) ⇒ (α ⇒ α)) id) id)
     ≡ just (α ⇒ α)
_ = refl

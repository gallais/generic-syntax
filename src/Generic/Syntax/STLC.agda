module Generic.Syntax.STLC where

open import Data.Product
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Function

open import var
open import Generic.Syntax

-- One base type, one function type constructor
data Type : Set where
  α    : Type
  _⇒_  : Type → Type → Type

-- Two constructors: Application and Lambda-abstraction
data `STLC : Set where
  App Lam : Type → Type → `STLC

-- Type-and-Scope safe definition of STLC
STLC : Desc Type
STLC =  `σ `STLC $ λ where
  (App σ τ) → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ))
  (Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ ⇒ τ))

module PATTERNS where

  -- Pattern synonyms
  pattern VAR x    = `var x
  pattern APP f t  = `con (App _ _ , f , t , refl)
  pattern LAM b    = `con (Lam _ _ , b , refl)

_ : TM STLC ((α ⇒ α) ⇒ (α ⇒ α))
_ = let open PATTERNS in
    LAM (LAM (APP (VAR (s z)) (VAR z)))

open PATTERNS
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Semantics.Development
open import Relation.Unary renaming (_⇒_ to _⟶_)

dev : ∀ {i} → ∀[ Tm STLC _ i ⟶ Tm STLC _ i ]
dev = development STLC λ σ → λ where
  (App _ _ , (LAM f) , t , refl) → f [ t /0]
  t                              → Sem.alg Substitution t

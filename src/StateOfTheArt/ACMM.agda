--------------------------------------------------------------------------------
-- This module demonstrates the similitudes between various semantics for STLC
-- before giving a generic notion of Scope-and-Type Safe Semantics à la
-- Type-and-scope Safe Programs and Their Proofs
-- (Allais, Chapman, McBride, and McKinna, CPP 17)
--------------------------------------------------------------------------------

module StateOfTheArt.ACMM where

open import indexed
open import var hiding (_<$>_ ; get)
open import environment as E hiding (_>>_ ; extend)

open import Data.Nat.Base
open import Data.List.Base hiding ([_] ; _++_ ; lookup)
open import Function

--------------------------------------------------------------------------------
-- Well scoped-and-typed Simply-Typed Lambda Calculus

infixr 3 _⇒_
data Type : Set where
  α    : Type
  _⇒_  : Type → Type → Type

data Lam : Type ─Scoped where
  V : {σ : Type} →    [ Var σ                ⟶ Lam σ        ]
  A : {σ τ : Type} →  [ Lam (σ ⇒ τ) ⟶ Lam σ  ⟶ Lam τ        ]
  L : {σ τ : Type} →  [ (σ ∷_) ⊢ Lam τ       ⟶ Lam (σ ⇒ τ)  ]

--------------------------------------------------------------------------------
-- Observation: the code of the traversals implementing renaming, substitution,
-- and normalization by evaluation looks the same!


-- Renaming
⟦V⟧‿ren : ∀ {n} → [ Var n ⟶ Lam n ]
⟦V⟧‿ren = V

extend‿ren : {Γ Δ : List Type} {σ : Type} → (Γ ─Env) Var Δ → (σ ∷ Γ ─Env) Var (σ ∷ Δ)
extend‿ren ρ = s <$> ρ ∙ z

ren : {Γ Δ : List Type} {σ : Type} → (Γ ─Env) Var Δ → Lam σ Γ → Lam σ Δ
ren ρ (V k)    = ⟦V⟧‿ren (lookup ρ k)
ren ρ (A f t)  = A (ren ρ f) (ren ρ t)
ren ρ (L b)    = L (ren (extend‿ren ρ) b)

-- Substitution
extend‿sub : {Γ Δ : List Type} {σ : Type} → (Γ ─Env) Lam Δ → (σ ∷ Γ ─Env) Lam (σ ∷ Δ)
extend‿sub ρ = ren E.extend <$> ρ ∙ V z

⟦V⟧‿sub : ∀ {n} → [ Lam n ⟶ Lam n ]
⟦V⟧‿sub x = x

sub : {Γ Δ : List Type} {σ : Type} → (Γ ─Env) Lam Δ → Lam σ Γ → Lam σ Δ
sub ρ (V k)    = ⟦V⟧‿sub (lookup ρ k)
sub ρ (A f t)  = A (sub ρ f) (sub ρ t)
sub ρ (L b)    = L (sub (extend‿sub ρ) b)


Val : Type ─Scoped
Val α       = Lam α
Val (σ ⇒ τ) = □ (Val σ ⟶ Val τ)

th^Val : (σ : Type) → Thinnable (Val σ)
th^Val α       = λ ρ t → ren t ρ
th^Val (σ ⇒ τ) = th^□

reify   : (σ : Type) → [ Val σ ⟶ Lam σ ]
reflect : (σ : Type) → [ Lam σ ⟶ Val σ ]

reify   α = id
reify   (σ ⇒ τ) = λ b → L (reify τ (b E.extend (reflect σ (V z))))

reflect α = id
reflect (σ ⇒ τ) = λ b ρ v → reflect τ (A (ren ρ b) (reify σ v))

extend‿nbe : {Γ Δ Θ : List Type} {σ : Type} →
         Thinning Δ Θ → (Γ ─Env) Val Δ → Val σ Θ → (σ ∷ Γ ─Env) Val Θ
extend‿nbe r ρ v = (λ {σ} v → th^Val σ v r) <$> ρ ∙ v

⟦V⟧‿nbe : ∀ {n Γ} → Var n Γ → [ Val n ⟶ Val n ]
⟦V⟧‿nbe _ x = x

⟦A⟧‿nbe : ∀ {σ τ Γ} → Lam (σ ⇒ τ) Γ → [ Val (σ ⇒ τ) ⟶ Val σ ⟶ Val τ ]
⟦A⟧‿nbe _ f t = extract f t

nbe : {Γ Δ : List Type} {σ : Type} → (Γ ─Env) Val Δ → Lam σ Γ → Val σ Δ
nbe ρ (V k)    = ⟦V⟧‿nbe k (lookup ρ k)
nbe ρ (A f t)  = ⟦A⟧‿nbe f (nbe ρ f) (nbe ρ t)
nbe ρ (L b)    = λ σ v → nbe (extend‿nbe σ ρ v) b

--------------------------------------------------------------------------------
-- A Generic Notion of Semantics and the corresponding generic traversal

record Sem (𝓥 𝓒 : Type ─Scoped) : Set where
  field  th^𝓥  : ∀ {σ} → Thinnable (𝓥 σ)
         ⟦V⟧   : {σ : Type} →               [ 𝓥 σ               ⟶ 𝓒 σ        ]
         ⟦A⟧   : {σ τ : Type} →             [ 𝓒 (σ ⇒ τ) ⟶ 𝓒 σ   ⟶ 𝓒 τ        ]
         ⟦L⟧   : (σ : Type) → {τ : Type} →  [ □ (𝓥 σ ⟶ 𝓒 τ)     ⟶ 𝓒 (σ ⇒ τ)  ]


  sem : {Γ Δ : List Type} {σ : Type} → (Γ ─Env) 𝓥 Δ → (Lam σ Γ → 𝓒 σ Δ)
  sem ρ (V k)    = ⟦V⟧ (lookup ρ k)
  sem ρ (A f t)  = ⟦A⟧ (sem ρ f) (sem ρ t)
  sem ρ (L b)    = ⟦L⟧ _ (λ σ v → sem (extend σ ρ v) b) where

   extend : {Γ Δ Θ : List Type} {σ : Type} →
            Thinning Δ Θ → (Γ ─Env) 𝓥 Δ → 𝓥 σ Θ → (σ ∷ Γ ─Env) 𝓥 Θ
   extend σ ρ v = (λ t → th^𝓥 t σ) <$> ρ ∙ v
open Sem

--------------------------------------------------------------------------------
-- Defining various traversals as instances of Sem

Renaming : Sem Var Lam
Renaming = record
  { th^𝓥  = th^Var
  ; ⟦V⟧    = V
  ; ⟦A⟧    = A
  ; ⟦L⟧    = λ σ b → L (b (pack s) z) }

Substitution : Sem Lam Lam
Substitution = record
   { th^𝓥  = λ t ρ → Sem.sem Renaming ρ t
   ; ⟦V⟧    = id
   ; ⟦A⟧    = A
   ; ⟦L⟧    = λ σ b → L (b (pack s) (V z)) }

open import Category.Monad.State
open import Category.Applicative
open import Data.String hiding (show)
open import Data.Nat.Show
open import Data.Product

module Printer where
 open RawMonadState (StateMonadState ℕ)

 record Wrap (A : Set) (σ : Type) (Γ : List Type) : Set where
   constructor MkW; field getW : A

 open Wrap public

 th^Wrap : {A : Set} → ∀ {σ} → Thinnable (Wrap A σ)
 th^Wrap w ρ = MkW (getW w)

 map^Wrap : {A B : Set} → ∀ {σ} → (A → B) → [ Wrap A σ ⟶ Wrap B σ ]
 map^Wrap f (MkW a) = MkW (f a)

 open E

 fresh : {Γ : List Type} → ∀ σ → State ℕ (Wrap String σ (σ ∷ Γ))
 fresh σ = get >>= λ x → MkW (show x) <$ put (suc x)

 Printing : Sem (Wrap String) (Wrap (State ℕ String))
 Printing = record
   { th^𝓥  =  th^Wrap
   ; ⟦V⟧    =  map^Wrap return
   ; ⟦A⟧    =  λ mf mt → MkW $ getW mf >>= λ f → getW mt >>= λ t →
               return $ f ++ "(" ++ t ++ ")"
   ; ⟦L⟧    =  λ σ mb → MkW $ fresh σ >>= λ x →
               getW (mb extend x) >>= λ b →
               return $ "λ" ++ getW x ++ "." ++ b }

-- Test runs of Printing as a semantics:
open Printer using (Printing)

print : (σ : Type) → Lam σ [] → String
print _ t = proj₁ $ Printer.getW (sem Printing {Δ = []} ε t) 0

open import Relation.Binary.PropositionalEquality

_ : print (α ⇒ α) (L (V z)) ≡ "λ0.0"
_ = refl

_ : print ((α ⇒ α) ⇒ (α ⇒ α)) (L (L (A (V (s z)) (A (V (s z)) (V z)))))
        ≡ "λ0.λ1.0(0(1))"
_ = refl

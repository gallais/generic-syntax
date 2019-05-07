{-# OPTIONS --safe --sized-types #-}

module StateOfTheArt.ACMM where

open import Data.Var hiding (_<$>_; get)
open import Data.Environment as E hiding (_>>_ ; extend)

open import Data.Nat.Base
open import Data.List.Base using (List; _∷_; [])
open import Function
open import Relation.Unary

private
  variable
    I : Set

infixr 3 _`→_

data Type : Set where
  α    : Type
  _`→_  : Type → Type → Type

private
  variable
    σ τ : I
    Γ Δ Θ : List I
    A B : Set


data Lam : Type ─Scoped where
  `var  : ∀[ Var σ ⇒ Lam σ ]
  `app  : ∀[ Lam (σ `→ τ) ⇒ Lam σ ⇒ Lam τ ]
  `lam  : ∀[ (σ ∷_) ⊢ Lam τ ⇒ Lam (σ `→ τ) ]

module Renaming where

 varᵣ : ∀[ Var σ ⇒ Lam σ ]
 varᵣ = `var

 extendᵣ : (Γ ─Env) Var Δ → (σ ∷ Γ ─Env) Var (σ ∷ Δ)
 extendᵣ ρ = s <$> ρ ∙ z

 ren : (Γ ─Env) Var Δ → Lam σ Γ → Lam σ Δ
 ren ρ (`var k)    = varᵣ (lookup ρ k)
 ren ρ (`app f t)  = `app (ren ρ f) (ren ρ t)
 ren ρ (`lam b)    = `lam (ren (extendᵣ ρ) b)

module Substitution where
 extendₛ : (Γ ─Env) Lam Δ → (σ ∷ Γ ─Env) Lam (σ ∷ Δ)
 extendₛ ρ = Renaming.ren E.extend <$> ρ ∙ `var z

 varₛ : ∀[ Lam σ ⇒ Lam σ ]
 varₛ x = x

 sub : (Γ ─Env) Lam Δ → Lam σ Γ → Lam σ Δ
 sub ρ (`var k)    = varₛ (lookup ρ k)
 sub ρ (`app f t)  = `app (sub ρ f) (sub ρ t)
 sub ρ (`lam b)    = `lam (sub (extendₛ ρ) b)

module _ where

 private
   Val : Type ─Scoped
   Val α       = Lam α
   Val (σ `→ τ) = □ (Val σ ⇒ Val τ)

   th^Val : (σ : Type) → Thinnable (Val σ)
   th^Val α       = λ ρ t → Renaming.ren t ρ
   th^Val (σ `→ τ) = th^□

   reify   : (σ : Type) → ∀[ Val σ ⇒ Lam σ ]
   reflect : (σ : Type) → ∀[ Lam σ ⇒ Val σ ]

   reify   α = id
   reify   (σ `→ τ) = λ b → `lam (reify τ (b E.extend (reflect σ (`var z))))

   reflect α = id
   reflect (σ `→ τ) = λ b ρ v → reflect τ (`app (Renaming.ren ρ b) (reify σ v))

   extendₙ : Thinning Δ Θ → (Γ ─Env) Val Δ → Val σ Θ → (σ ∷ Γ ─Env) Val Θ
   extendₙ r ρ v = (λ {σ} v → th^Val σ v r) <$> ρ ∙ v

   varₙ : Var σ Γ → ∀[ Val σ ⇒ Val σ ]
   varₙ _ x = x

   appₙ : Lam (σ `→ τ) Γ → ∀[ Val (σ `→ τ) ⇒ Val σ ⇒ Val τ ]
   appₙ _ f t = f (pack id) t

 nbe : (Γ ─Env) Val Δ → Lam σ Γ → Val σ Δ
 nbe ρ (`var k)    = varₙ k (lookup ρ k)
 nbe ρ (`app f t)  = appₙ f (nbe ρ f) (nbe ρ t)
 nbe ρ (`lam b)    = λ σ v → nbe (extendₙ σ ρ v) b

record Semantics (𝓥 𝓒 : Type ─Scoped) : Set where

  field

    th^𝓥  : Thinnable (𝓥 σ)

    var   : ∀[ 𝓥 σ ⇒ 𝓒 σ ]

    app   : ∀[ 𝓒 (σ `→ τ) ⇒ 𝓒 σ ⇒ 𝓒 τ ]

    lam   : ∀[ □ (𝓥 σ ⇒ 𝓒 τ) ⇒ 𝓒 (σ `→ τ) ]

  extend : Thinning Δ Θ → (Γ ─Env) 𝓥 Δ → 𝓥 σ Θ → (σ ∷ Γ ─Env) 𝓥 Θ
  extend σ ρ v = (λ t → th^𝓥 t σ) <$> ρ ∙ v

  semantics : (Γ ─Env) 𝓥 Δ → (Lam σ Γ → 𝓒 σ Δ)

  semantics ρ (`var k)    = var (lookup ρ k)
  semantics ρ (`app f t)  = app (semantics ρ f) (semantics ρ t)
  semantics ρ (`lam b)    = lam (λ σ v → semantics (extend σ ρ v) b)

open E using (extend)

Renaming : Semantics Var Lam
Renaming = record
  { th^𝓥  = th^Var
  ; var   = `var
  ; app   = `app
  ; lam   = λ b → `lam (b extend z) }

ren : (Γ ─Env) Var Δ → Lam σ Γ → Lam σ Δ
ren = Semantics.semantics Renaming

Substitution : Semantics Lam Lam
Substitution = record
   { th^𝓥  = λ t ρ → ren ρ t
   ; var   = id
   ; app   = `app
   ; lam   = λ b → `lam (b extend (`var z)) }

sub : (Γ ─Env) Lam Δ → Lam σ Γ → Lam σ Δ
sub = Semantics.semantics Substitution

open import Category.Monad.State
open import Category.Applicative
open import Data.String hiding (show)
open import Data.Nat.Show
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

module Printer where
 open import Codata.Stream as Stream using (Stream; _∷_; head; tail)
 open RawMonadState (StateMonadState (Stream String _))

 M : Set → Set
 M = State (Stream String _)

 record Wrap (A : Set) (σ : I) (Γ : List I) : Set where
   constructor MkW; field getW : A

 open Wrap public

 Name : I ─Scoped
 Name = Wrap String

 Printer : I ─Scoped
 Printer = Wrap (M String)


 th^Wrap : Thinnable {I} (Wrap A σ)
 th^Wrap w ρ = MkW (getW w)

 map^Wrap : (A → B) → ∀[ Wrap A σ ⇒ Wrap B σ ]
 map^Wrap f (MkW a) = MkW (f a)

 open E hiding (_>>_)

 fresh : ∀ σ → M (Name σ (σ ∷ Γ))
 fresh σ = do
   names ← get
   put (tail names)
   pure (MkW (head names))

 Printing : Semantics Name Printer
 Printing = record
   { th^𝓥  =  th^Wrap
   ; var   =  map^Wrap return
   ; app   =  λ mf mt → MkW $ getW mf >>= λ f → getW mt >>= λ t →
              return $ f ++ " (" ++ t ++ ")"
   ; lam   =  λ {σ} mb → MkW $ fresh σ >>= λ x →
              getW (mb extend x) >>= λ b →
              return $ "λ" ++ getW x ++ ". " ++ b }

 open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
 open import Codata.Thunk using (force)
 import Data.Nat.Show as NatShow

 alphabetWithSuffix : String → List⁺ String
 alphabetWithSuffix suffix = List⁺.map (λ c → fromList (c ∷ []) ++ suffix)
                           $′ 'a' ∷ toList "bcdefghijklmnopqrstuvwxyz"

 allNats : Stream ℕ _
 allNats = Stream.iterate suc 0

 names : Stream String _
 names = Stream.concat
       $′ Stream.map alphabetWithSuffix
       $′ "" ∷ λ where .force → Stream.map NatShow.show allNats

open Printer using (Printing)

print : (σ : Type) → Lam σ [] → String
print _ t = proj₁ $ Printer.getW (Semantics.semantics Printing {Δ = []} (pack λ ()) t) Printer.names

_ : print (α `→ α) (`lam (`var z)) ≡ "λa. a"
_ = refl

module _ {σ τ : Type} where


  apply : Lam ((σ `→ τ) `→ (σ `→ τ)) []
  apply =  `lam {- f -} $ `lam {- x -}
        $  `app (`var (s z) {- f -}) (`var z {- x -})


  _ : print _ apply ≡ "λa. λb. a (b)"
  _ = refl


_ : print ((α `→ α) `→ (α `→ α)) (`lam (`lam (`app (`var (s z)) (`app (`var (s z)) (`var z))))) ≡ "λa. λb. a (a (b))"
_ = refl

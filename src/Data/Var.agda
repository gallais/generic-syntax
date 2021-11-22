{-# OPTIONS --safe #-}

-- When scopes are represented by lists of kinds, a variable of
-- a given kind is a position in such a list. This is a strongly
-- typed version of de Bruijn indices hence the name we picked
-- for Var's constructor:
-- * z for zero
-- * s for successor

module Data.Var where

open import Data.Sum hiding (map)
open import Data.List.Base hiding ([_]; _─_)
open import Data.List.Relation.Unary.All using (All ; _∷_)
open import Relation.Unary
open import Function.Base
open import Agda.Builtin.Equality


_─Scoped : Set → Set₁
I ─Scoped = I → List I → Set


private
  variable
    I J : Set
    σ τ : I


data Var : I ─Scoped where
  z : ∀[ (σ ∷_) ⊢ Var σ ]
  s : ∀[ Var σ ⇒ (τ ∷_) ⊢ Var σ ]

infixl 3 _─_
_─_ : {σ : I} (Γ : List I) → Var σ Γ → List I
_ ∷ Γ ─ z   = Γ
σ ∷ Γ ─ s v = σ ∷ (Γ ─ v)

get : {B : I → Set} → ∀[ Var σ ⇒ All B ⇒ const (B σ) ]
get z     (b  ∷ _)  = b
get (s v) (_  ∷ bs) = get v bs

_<$>_ : (f : I → J) → ∀[ Var σ ⇒ map f ⊢ Var (f σ) ]
f <$> z    = z
f <$> s v  = s (f <$> v)

record Injective (f : I → J) : Set where
  constructor mkInjective
  field inj : ∀ {i₁ i₂} → f i₁ ≡ f i₂ → i₁ ≡ i₂
open Injective public

Injective-inj₁ : ∀ {A B : Set} → Injective ((A → A ⊎ B) ∋ inj₁)
inj Injective-inj₁ refl = refl

Injective-inj₂ : ∀ {A B : Set} → Injective ((B → A ⊎ B) ∋ inj₂)
inj Injective-inj₂ refl = refl

_<$>⁻¹_ : {f : I → J} → Injective f →
          ∀[ map f ⊢ Var (f σ) ⇒ Var σ ]
_<$>⁻¹_ {f = f} F = go _ refl refl where

  go : ∀ {j} Γ {js} → f σ ≡ j → map f Γ ≡ js → Var j js → Var σ Γ
  go []        eq ()   z
  go []        eq ()   (s v)
  go (i ∷ is)  eq refl z rewrite inj F eq = z
  go (i ∷ is)  eq refl (s v) = s (go is eq refl v)

injectˡ : ∀ Δ → ∀[ Var σ ⇒ (_++ Δ) ⊢ Var σ ]
injectˡ k z      = z
injectˡ k (s v)  = s (injectˡ k v)

injectʳ : ∀ Δ → ∀[ Var σ ⇒ (Δ ++_) ⊢ Var σ ]
injectʳ []        v = v
injectʳ (y ∷ ys)  v = s (injectʳ ys v)

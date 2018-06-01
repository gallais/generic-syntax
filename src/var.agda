-- When scopes are represented by lists of kinds, a variable of
-- a given kind is a position in such a list. This is a strongly
-- typed version of de Bruijn indices hence the name we picked
-- for Var's constructor:
-- * z for zero
-- * s for successor

module var where

open import indexed
open import Data.Sum hiding (map)
open import Data.List.Base hiding ([_])
open import Data.List.All using (All ; _∷_)
open import Function
open import Agda.Builtin.Equality

_─Scoped : Set → Set₁
I ─Scoped = I → List I → Set

module _ {I : Set} where

 data Var : I ─Scoped where
   z : {i : I} →    [          (i ∷_) ⊢ Var i ]
   s : {i j : I} →  [ Var i ⟶  (j ∷_) ⊢ Var i ]

 infixl 3 _─_
 _─_ : {i : I} (Γ : List I) → Var i Γ → List I
 _ ∷ Γ ─ z   = Γ
 σ ∷ Γ ─ s v = σ ∷ (Γ ─ v)

 get : {B : I → Set} {i : I} → [ Var i ⟶ All B ⟶ κ (B i) ]
 get z     (b  ∷ _)  = b
 get (s v) (_  ∷ bs) = get v bs

_<$>_ : {I J : Set} (f : I → J) {i : I} → [ Var i ⟶ Var (f i) ∘ map f ]
f <$> z    = z
f <$> s v  = s (f <$> v)

record Injective {I J : Set} (f : I → J) : Set where
  constructor mkInjective
  field inj : ∀ {i₁ i₂} → f i₁ ≡ f i₂ → i₁ ≡ i₂
open Injective public

Injective-inj₁ : ∀ {A B : Set} → Injective ((A → A ⊎ B) ∋ inj₁)
inj Injective-inj₁ refl = refl

Injective-inj₂ : ∀ {A B : Set} → Injective ((B → A ⊎ B) ∋ inj₂)
inj Injective-inj₂ refl = refl

_<$>⁻¹_ : {I J : Set} {f : I → J} → Injective f →
          {i : I} → [ Var (f i) ∘ map f ⟶ Var i ]
_<$>⁻¹_ {I} {J} {f} F = go _ refl refl where

  go : {i : I} {j : J} (is : List I) {js : List J} →
       f i ≡ j → map f is ≡ js → Var j js → Var i is
  go []        eq ()   z
  go []        eq ()   (s v)
  go (i ∷ is)  eq refl z rewrite inj F eq = z
  go (i ∷ is)  eq refl (s v) = s (go is eq refl v)

injectˡ : {I : Set} {i : I} (ys : List I) → [ Var i ⟶ (_++ ys) ⊢ Var i ]
injectˡ k z      = z
injectˡ k (s v)  = s (injectˡ k v)

injectʳ : {I : Set} {i : I} (ys : List I) → [ Var i ⟶ (ys ++_) ⊢ Var i ]
injectʳ []        v = v
injectʳ (y ∷ ys)  v = s (injectʳ ys v)

--------------------------------------------------------------------------------
-- This module implements a Universe of Data Types à la
-- The Gentle Art of Levitation
-- (Chapman, Dagand, McBride, and Morris, ICFP 10)
--------------------------------------------------------------------------------

module StateOfTheArt.CDMM where

open import indexed
open import Size
open import Data.Empty
open import Data.Bool
open import Data.Nat using (ℕ ; suc)
open import Data.Unit
open import Data.Product as Prod
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

data Desc (I J : Set) : Set₁ where
  `σ : (A : Set) → (A → Desc I J)  →  Desc I J
  `X : J → Desc I J                →  Desc I J
  `∎ : I                           →  Desc I J

module _ {I J : Set} where
 infixr 5 _`+_

 `K : Set → I → Desc I J
 `K A i = `σ A (λ _ → `∎ i)

 _`+_ : Desc I J → Desc I J → Desc I J
 d `+ e = `σ Bool $ λ { true  → d ; false → e }

 ⟦_⟧ : Desc I J → (J → Set) → (I → Set)
 ⟦ `σ A d  ⟧ X i = Σ[ a ∈ A ] (⟦ d a ⟧ X i)
 ⟦ `X j d  ⟧ X i = X j × ⟦ d ⟧ X i
 ⟦ `∎ i′   ⟧ X i = i ≡ i′

 fmap : {X Y : J → Set} → (d : Desc I J) → [ X ⟶ Y ] → [ ⟦ d ⟧ X ⟶ ⟦ d ⟧ Y ]
 fmap (`σ A d)  f (a , v)  = (a , fmap (d a) f v)
 fmap (`X j d)  f (r , v)  = (f r , fmap d f v)
 fmap (`∎ i)    f t        = t

data μ {I : Set} (d : Desc I I) : Size → I → Set where
  `con : {i : I} {s : Size} → ⟦ d ⟧ (μ d s) i → μ d (↑ s) i

fold : {I : Set} {X : I → Set} {s : Size} → (d : Desc I I) → [ ⟦ d ⟧ X ⟶ X ] → [ μ d s ⟶ X ]
fold d alg (`con t) = alg (fmap d (fold d alg) t)

finD : Desc ℕ ℕ
finD =  `σ ℕ $ λ index →
        `σ Bool $ λ isZero → if isZero
        then `∎ (suc index)
        else `X index (`∎ (suc index))

fin : ℕ → Set
fin = μ finD ∞

fin0-elim : fin 0 → ⊥
fin0-elim (`con (_ , true , ()))
fin0-elim (`con (_ , false , _ , ()))

fz : ∀ n → fin (suc n)
fz n = `con (n , true , refl)

fs : ∀ n → fin n → fin (suc n)
fs n k = `con (n , false , k , refl)

listD : Set → Desc ⊤ ⊤
listD A =  `σ Bool $ λ isNil →
           if isNil then `∎ tt
           else `σ A (λ _ → `X tt (`∎ tt))

List : Set → Set
List A = μ (listD A) ∞ tt

[] : {A : Set} → μ (listD A) ∞ tt
[] = `con (true , refl)

infixr 10 _∷_

_∷_ : {A : Set} → A → List A → List A
x ∷ xs = `con (false , x , xs , refl)

example : List (List Bool)
example  = (false ∷ []) ∷ (true ∷ []) ∷ []

vecD : Set → Desc ℕ ℕ
vecD A =  `σ Bool $ λ isNil →
          if isNil then `∎ 0
          else `σ ℕ (λ n → `σ A (λ _ → `X n (`∎ (suc n))))

Vec : Set → ℕ → Set
Vec A = μ (vecD A) ∞

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr {A} {B} c n = fold (listD A) alg where

  alg : ⟦ listD A ⟧ (const B) tt → B
  alg (true             , refl)  = n
  alg (false , hd , rec , refl)  = c hd rec

_++_ : {A : Set} → List A  → List A → List A
_++_ = foldr (λ hd rec → hd ∷_ ∘ rec) id

flatten : {A : Set} → List (List A) → List A
flatten = foldr _++_ []

test : flatten example ≡ false ∷ true ∷ []
test = refl

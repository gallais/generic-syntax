{-# OPTIONS --safe --sized-types #-}
module Generic.Examples.Colist where

open import Size
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Agda.Builtin.Equality

open import Data.Var
open import Data.Environment
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Cofinite
open import Generic.Bisimilar hiding (refl)

module _  where
 open import Data.List.Base

 CListD : Set → Desc ⊤
 CListD A  =   `∎ tt
           `+  `σ A (λ _ → `X (tt ∷ []) tt (`∎ tt))

infixr 5 _∷_

pattern []        = `con (true , refl)
pattern _∷_ x xs  = `con (false , x , xs , refl)
pattern ↶_ k      = `var k

[0,1]  : TM (CListD ℕ) tt
01↺    : TM (CListD ℕ) tt

[0,1]  =  0 ∷ 1 ∷ []
01↺    =  0 ∷ 1 ∷ ↶ s z

mutual

 01⋯ : ∀ {s} → ∞Tm (CListD ℕ) s tt
 01⋯ .force = false , 0 , 10⋯ , refl

 10⋯ : ∀ {s} → ∞Tm (CListD ℕ) s tt
 10⋯ .force = false , 1 , 01⋯ , refl

`1∷2∷3 : TM (CListD ℕ) tt
`1∷2∷3 = 1 ∷ 2 ∷ 3 ∷ []

`1∷2⇖1 : TM (CListD ℕ) tt
`1∷2⇖1 = 1 ∷ 2 ∷ ↶ s z

∞1∷2 : ∀ {s} → ∞Tm (CListD ℕ) s tt
∞2∷1 : ∀ {s} → ∞Tm (CListD ℕ) s tt
∞Tm.force ∞1∷2 = (false , 1 , ∞2∷1 , refl)
∞Tm.force ∞2∷1 = (false , 2 , ∞1∷2 , refl)

-- Proofs about the simple example: Potentially cyclic lists

eq-01 : {i : Size} → ≈^∞Tm (CListD ℕ) i tt 01⋯ (unfold 01↺)
eq-10 : {i : Size} → ≈^∞Tm (CListD ℕ) i tt 10⋯ (unfold (1 ∷ 0 ∷ 1 ∷ ↶ s z))

eq-01 .force = refl , refl , eq-10 , tt
eq-10 .force = refl , refl , eq-01 , tt

eq₁ : ∀ {s} → ≈^∞Tm (CListD ℕ) s tt ∞1∷2 (unfold `1∷2⇖1)
eq₂ : ∀ {s} → ≈^∞Tm (CListD ℕ) s tt ∞2∷1 (unfold (2 ∷ (th^Tm `1∷2⇖1 ε)))

≈^∞Tm.force eq₁ = _≡_.refl , _≡_.refl , eq₂ , tt
≈^∞Tm.force eq₂ = _≡_.refl , _≡_.refl , eq₁ , tt

{-# OPTIONS --safe --sized-types #-}
module Generic.Cofinite where

open import Size
open import Data.Unit
open import Data.List.Base hiding (unfold)

open import Data.Var using (_─Scoped)
open import Data.Environment
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic

private
  variable
    I : Set
    s : Size



Const : (I → Set) → List I → I ─Scoped
Const T Δ j Γ = T j

record ∞Tm (d : Desc I) (s : Size) (i : I) : Set where
  coinductive; constructor `con
  field force :  {s' : Size< s} →
                 ⟦ d ⟧ (Const (∞Tm d s')) i []

open ∞Tm public

module _ {d : Desc ⊤} where

  plug : TM d tt → ∀ Δ i → Scope (Tm d ∞) Δ i [] → TM d i
  plug t Δ i = Semantics.semantics Sub (pack (λ _ → t))

  unroll : TM d tt → ⟦ d ⟧ (Const (TM d)) tt []
  unroll t@(`con b) = fmap d (plug t) b

  unfold : TM d tt → ∞Tm d s tt
  unfold t .force = fmap d (λ _ _ → unfold) (unroll t)

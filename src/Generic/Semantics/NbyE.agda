module Generic.Semantics.NbyE where

import Level
open import Size
import Category.Monad as CM
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.List.Base hiding ([_])
open import Data.Maybe.Base
open import Data.Maybe.Categorical as MC
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import indexed
open import var
open import varlike
open import environment hiding (traverse)
open import Generic.Syntax
open import Generic.Semantics


{-# NO_POSITIVITY_CHECK #-}
data Dm {I : Set} (d : Desc I) : Size → I ─Scoped where
  V : {s : Size} {i : I} → [ Var i                               ⟶  Dm d s      i  ]
  C : {s : Size} {i : I} → [ ⟦ d ⟧ (Kripke (Dm d s) (Dm d s)) i  ⟶  Dm d (↑ s)  i  ]
  ⊥ : {s : Size} {i : I} → [                                        Dm d (↑ s)   i  ]

module _ {I : Set} {d : Desc I} where

 th^Dm : {s : Size} {i : I} → Thinnable (Dm d s i)
 th^Dm (V k) ρ = V (th^Var k ρ)
 th^Dm (C t) ρ = C (fmap d (λ Θ i kr → th^Kr Θ th^Dm kr ρ) t)
 th^Dm ⊥     ρ = ⊥

 vl^Dm : {s : Size} → VarLike (Dm d s)
 vl^Dm = record { new = V z ; th^𝓥 = th^Dm }

module M = CM.RawMonad (MC.monad {Level.zero})
open M

module _ {I : Set} {d : Desc I} where

 reify^Dm  : {s : Size} {i : I} → [ Dm d s i ⟶ Maybe ∘ Tm d ∞ i ]
 nbe       : Alg d (Dm d ∞) (Dm d ∞) → Sem d (Dm d ∞) (Dm d ∞)

 norm      : Alg d (Dm d ∞) (Dm d ∞) → {i : I} → [ Tm d ∞ i ⟶ Maybe ∘ Tm d ∞ i ]
 norm alg  = reify^Dm ∘ Sem.sem (nbe alg) (base vl^Dm)

 reify^Dm (V k) = just (`var k)
 reify^Dm (C v) = `con M.<$> traverse (CM.RawMonad.rawIApplicative MC.monad) d
                            (fmap d (λ Θ i → reify^Dm ∘ reify vl^Dm Θ i) v)
 reify^Dm ⊥     = nothing

 Sem.th^𝓥  (nbe alg) = th^Dm
 Sem.var   (nbe alg) = id
 Sem.alg   (nbe alg) = alg

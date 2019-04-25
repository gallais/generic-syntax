\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Bisimilar where

open import Size
open import Data.Unit
open import Data.Bool
open import Data.Nat.Base
open import Data.Fin
open import Data.Product

open import Data.Environment
open import Generic.Syntax
open import Generic.Cofinite
open import Generic.Relator
open import Generic.Simulation

open import Relation.Binary.PropositionalEquality using (_≡_ ; subst)

private
  variable
    I : Set
\end{code}

%<*bisim>
\begin{code}
record ≈^∞Tm (d : Desc I) (s : Size) (i : I) (t u : ∞Tm d s i) : Set where
  coinductive
  field force : {s′ : Size< s} → ⟦ d ⟧ᴿ (λ _ i → ≈^∞Tm d s′ i) (t .force) (u .force)
\end{code}
%</bisim>

\begin{code}
open ≈^∞Tm public
module _ {I : Set} (d : Desc I) where

 private
  variable
    s : Size
    i : I
    t u v : ∞Tm d s i
\end{code}

%<*eqrel>
\begin{code}
 refl  : ≈^∞Tm d s i t t
 sym   : ≈^∞Tm d s i t u → ≈^∞Tm d s i u t
 trans : ≈^∞Tm d s i t u → ≈^∞Tm d s i u v → ≈^∞Tm d s i t v
\end{code}
%</eqrel>
\begin{code}
 ≈^∞Tm.force refl = reflᴿ d (λ _ _ _ → refl) _
 ≈^∞Tm.force (sym eq) = symᴿ d (λ _ _ → sym) (≈^∞Tm.force eq)
 ≈^∞Tm.force (trans t≈u u≈v) = transᴿ d (λ _ _ → trans) (≈^∞Tm.force t≈u) (≈^∞Tm.force u≈v)
\end{code}


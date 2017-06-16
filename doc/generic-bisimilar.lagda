\begin{code}
module generic-bisimilar where

open import Size
open import Data.Unit
open import Data.Bool
open import Data.Nat.Base
open import Data.Fin
open import Data.Product hiding (zip)

open import indexed
open import environment hiding (refl)
open import generic-syntax
open import generic-cofinite
open import generic-simulation

open import Relation.Binary.PropositionalEquality using (_≡_ ; subst)
\end{code}


%<*bisim>
\begin{code}
record ≈^∞Tm {I : Set} (d : Desc I) (s : Size) (i : I) (t u : ∞Tm d s i) : Set where
  coinductive; field force : {s′ : Size< s} → Zip d (λ _ i → ≈^∞Tm d s′ i) (∞Tm.force t) (∞Tm.force u)
\end{code}
%</bisim>

\begin{code}
module _ {I : Set} (d : Desc I) where
\end{code}

%<*eqrel>
\begin{code}
 refl  : {s : Size} {i : I} {t : ∞Tm d s i} → ≈^∞Tm d s i t t
 sym   : {s : Size} {i : I} {t u : ∞Tm d s i} → ≈^∞Tm d s i t u → ≈^∞Tm d s i u t
 trans : {s : Size} {i : I} {t u v : ∞Tm d s i} → ≈^∞Tm d s i t u → ≈^∞Tm d s i u v → ≈^∞Tm d s i t v
\end{code}
%</eqrel>
\begin{code}
 ≈^∞Tm.force refl = refl^Zip (λ _ _ _ → refl) d _
 ≈^∞Tm.force (sym eq) = sym^Zip (λ _ _ → sym) d (≈^∞Tm.force eq)
 ≈^∞Tm.force (trans t≈u u≈v) = trans^Zip (λ _ _ → trans) d (≈^∞Tm.force t≈u) (≈^∞Tm.force u≈v)
\end{code}

\begin{code}
-- Proofs about the simple example: Potentially cyclic lists

eq₁ : ∀ {s} → ≈^∞Tm (`listD ℕ) s tt ∞1∷2 (unfold `1∷2⇖1)
eq₂ : ∀ {s} → ≈^∞Tm (`listD ℕ) s tt ∞2∷1 (unfold (cons 2 (th^Tm `1∷2⇖1 ε)))

≈^∞Tm.force eq₁ = _≡_.refl , _≡_.refl , eq₂ , tt
≈^∞Tm.force eq₂ = _≡_.refl , _≡_.refl , eq₁ , tt
\end{code}


\begin{code}
open import Size
open import Data.Unit
open import Data.Bool
open import Data.Nat.Base
open import Data.Fin
open import Data.Product hiding (zip)

open import indexed
open import environment hiding (refl)
open import generic-syntax hiding (refl)
open import generic-cofinite
open import generic-simulation

open import Relation.Binary.PropositionalEquality using (_≡_ ; subst)
\end{code}


%<*bisim>
\begin{code}
record ≈^∞Tm (d : Desc) (i : Size) (t u : ∞Tm d i) : Set where
  coinductive; field force : {j : Size< i} → Zip d (λ _ → ≈^∞Tm d j) (∞Tm.force t) (∞Tm.force u)
\end{code}
%</bisim>

\begin{code}
module _ (d : Desc) where
\end{code}

%<*eqrel>
\begin{code}
 refl  : {i : Size} {t : ∞Tm d i} → ≈^∞Tm d i t t
 sym   : {i : Size} {t u : ∞Tm d i} → ≈^∞Tm d i t u → ≈^∞Tm d i u t
 trans : {i : Size} {t u v : ∞Tm d i} → ≈^∞Tm d i t u → ≈^∞Tm d i u v → ≈^∞Tm d i t v
\end{code}
%</eqrel>
\begin{code}
 ≈^∞Tm.force refl = refl^Zip (λ _ _ → refl) d _
 ≈^∞Tm.force (sym eq) = sym^Zip (λ _ → sym) d (≈^∞Tm.force eq)
 ≈^∞Tm.force (trans t≈u u≈v) = trans^Zip (λ _ → trans) d (≈^∞Tm.force t≈u) (≈^∞Tm.force u≈v)
\end{code}


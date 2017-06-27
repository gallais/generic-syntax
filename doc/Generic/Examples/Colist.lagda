\begin{code}
module Generic.Examples.Colist where

open import Size
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Agda.Builtin.Equality

open import var
open import environment hiding (refl)
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Cofinite
open import Generic.Bisimilar hiding (refl)

module _ where
 open import Data.List.Base
\end{code}
%<*clistD>
\begin{code}
 CListD : Set → Desc ⊤
 CListD A  =   `∎ tt
           `+  `σ A (λ _ → `X (tt ∷ []) tt (`∎ tt))
\end{code}
%</clistD>
\begin{code}
infixr 5 _∷_
\end{code}
%<*clistpat>
\begin{code}
pattern []        = `con (true , refl)
pattern _∷_ x xs  = `con (false , x , xs , refl)
pattern ↶_ k      = `var k
\end{code}
%</clistpat>
%<*zeroones>
\begin{code}
[0,1]  : TM (CListD ℕ) tt
01↺    : TM (CListD ℕ) tt

[0,1]  =  0 ∷ 1 ∷ []
01↺    =  0 ∷ 1 ∷ ↶ s z
\end{code}
%</zeroones>

%<*zeroones2>
\begin{code}
01⋯ : ∞Tm (CListD ℕ) ∞ tt
10⋯ : ∞Tm (CListD ℕ) ∞ tt
∞Tm.force 01⋯ = false , 0 , 10⋯ , refl
∞Tm.force 10⋯ = false , 1 , 01⋯ , refl
\end{code}
%</zeroones2>

\begin{code}
`1∷2∷3 : TM (CListD ℕ) tt
`1∷2∷3 = 1 ∷ 2 ∷ 3 ∷ []

`1∷2⇖1 : TM (CListD ℕ) tt
`1∷2⇖1 = 1 ∷ 2 ∷ ↶ s z

∞1∷2 : ∞Tm (CListD ℕ) ∞ tt
∞2∷1 : ∞Tm (CListD ℕ) ∞ tt

∞Tm.force ∞1∷2 = (false , 1 , ∞2∷1 , refl)
∞Tm.force ∞2∷1 = (false , 2 , ∞1∷2 , refl)
\end{code}

\begin{code}
-- Proofs about the simple example: Potentially cyclic lists

eq₁ : ∀ {s} → ≈^∞Tm (CListD ℕ) s tt ∞1∷2 (unfold `1∷2⇖1)
eq₂ : ∀ {s} → ≈^∞Tm (CListD ℕ) s tt ∞2∷1 (unfold (2 ∷ (th^Tm `1∷2⇖1 ε)))

≈^∞Tm.force eq₁ = _≡_.refl , _≡_.refl , eq₂ , tt
≈^∞Tm.force eq₂ = _≡_.refl , _≡_.refl , eq₁ , tt
\end{code}

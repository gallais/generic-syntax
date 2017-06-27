\begin{code}
module generic-cofinite where

open import Size
open import Data.Unit
open import Data.Nat.Base
open import Data.Bool
open import Data.Fin
open import Data.Product

open import indexed
open import var
open import environment hiding (refl)
open import generic-syntax

open import Relation.Binary.PropositionalEquality
module _ where
 open import Data.List.Base

 TM : {I : Set} → Desc I → I → Set
 TM d i = Tm d ∞ i []
\end{code}
%<*clistD>
\begin{code}
 CListD : Set → Desc ⊤
 CListD A  =   `∎ tt
           `+  `σ A (λ _ → `X (tt ∷ []) tt (`∎ tt))
\end{code}
%</clistD>
\begin{code}
module _ {I : Set} where
 open import Data.List.Base
\end{code}
%<*cotm>
\begin{code}
 record ∞Tm (d : Desc I) (s : Size) (i : I) : Set where
   coinductive
   constructor `con
   field force : {s′ : Size< s} → ⟦ d ⟧ (λ _ i _ → ∞Tm d s′ i) i []
\end{code}
%</cotm>
\begin{code}
module _ {d : Desc ⊤} where
 open import Data.List.Base hiding (unfold)
\end{code}
%<*plug>
\begin{code}
 plug : TM d tt → ∀ Δ i → Scope (Tm d ∞) Δ i [] → TM d i
 plug t Δ i = Sem.sem (Substitution d) (pack (λ _ → t))
\end{code}
%</plug>
%<*unroll>
\begin{code}
 unroll : TM d tt → ⟦ d ⟧ (λ _ i _ → TM d i) tt []
 unroll t′@(`con t) = fmap d (plug t′) t
\end{code}
%</unroll>
\begin{code}
 unroll t′@(`var ())
\end{code}
%<*unfold>
\begin{code}
 unfold : {s : Size} → TM d tt → ∞Tm d s tt
 ∞Tm.force (unfold t′) = fmap d (λ _ _ → unfold) (unroll t′)
\end{code}
%</unfold>
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

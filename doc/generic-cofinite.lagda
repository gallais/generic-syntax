\begin{code}
module generic-cofinite where

open import Size
open import Data.Unit
open import Data.Bool
open import Data.Fin
open import Data.List hiding (unfold)
open import Data.Product

open import indexed
open import var
open import environment hiding (refl)
open import generic-syntax

open import Relation.Binary.PropositionalEquality

TM : {I : Set} → Desc I → I → Set
TM d i = Tm d ∞ i []
\end{code}
%<*clistD>
\begin{code}
CListD : Set → Desc ⊤
CListD A = `∎ tt `+ `σ A (λ _ → `X (tt ∷ []) tt (`∎ tt))
\end{code}
%</clistD>
\end{code}
%<*zeroones>
\begin{code}
01↺ : TM (CListD ⊤) tt
01↺  =  `con (false , tt , `con (false , tt
     ,  `var (s z) , refl) , refl)
\end{code}
%</zeroones>
\begin{code}
module _ {I : Set} where
\end{code}
%<*cotm>
\begin{code}
 record ∞Tm (d : Desc I) (s : Size) (i : I) : Set where
   coinductive
   constructor `con
   field force : {s′ : Size< s} → ⟦ d ⟧ (λ _ i _ → ∞Tm d s′ i) i []
\end{code}
%</cotm>
%<*zeroones2>
\begin{code}
01⋯ : ∞Tm (CListD ⊤) ∞ tt
10⋯ : ∞Tm (CListD ⊤) ∞ tt
∞Tm.force 01⋯ = false , tt , 10⋯ , refl
∞Tm.force 10⋯ = false , tt , 01⋯ , refl
\end{code}
%</zeroones2>
\begin{code}
module _ {d : Desc ⊤} where
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
-- Simple example: Potentially cyclic lists

`listD : Set → Desc ⊤
`listD A = `∎ tt                              -- nil
        `+ `σ A λ _ → `X (tt ∷ []) tt (`∎ tt) -- cons (includes pointer declaration)

pattern nil       = `con (true , refl) 
pattern cons x xs = `con (false , x , xs , refl)

open import Data.Nat

`1∷2∷3 : TM (`listD ℕ) tt
`1∷2∷3 = cons 1 (cons 2 (cons 3 nil))

`1∷2⇖1 : TM (`listD ℕ) tt
`1∷2⇖1 = cons 1 (cons 2 (`var (s z)))

∞1∷2 : ∞Tm (`listD ℕ) ∞ tt
∞2∷1 : ∞Tm (`listD ℕ) ∞ tt

∞Tm.force ∞1∷2 = (false , 1 , ∞2∷1 , refl)
∞Tm.force ∞2∷1 = (false , 2 , ∞1∷2 , refl)
\end{code}

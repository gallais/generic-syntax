\begin{code}
open import Size
open import Data.Unit
open import Data.Bool
open import Data.Nat.Base
open import Data.Fin
open import Data.Product

open import indexed
open import environment
open import generic-syntax

open import Relation.Binary.PropositionalEquality using (_≡_ ; subst)


TM : Desc → Set
TM d = Tm d ∞ 0
\end{code}
%<*clistD>
\begin{code}
CListD : Set → Desc
CListD A = `∎ `+ `σ A (λ _ → `X 1 `∎)
\end{code}
%</clistD>
\end{code}
%<*zeroones>
\begin{code}
01↺ : TM (CListD ℕ)
01↺  =  `con (false , 0 , `con (false , 1
     ,  `var (suc zero) , _) , _)
\end{code}
%</zeroones>
%<*cotm>
\begin{code}
record ∞Tm (d : Desc) (i : Size) : Set where
  coinductive
  constructor `con
  field force : {j : Size< i} → ⟦ d ⟧ (λ _ _ → ∞Tm d j) 0
\end{code}
%</cotm>
%<*zeroones2>
\begin{code}
01⋯ : ∞Tm (CListD ℕ) ∞
10⋯ : ∞Tm (CListD ℕ) ∞
∞Tm.force 01⋯ = false , 0 , 10⋯ , _
∞Tm.force 10⋯ = false , 1 , 01⋯ , _
\end{code}
%</zeroones2>
\begin{code}
module _ {d : Desc} where
\end{code}
%<*plug>
\begin{code}
 plug : TM d → ∀ m → Scope (Tm d ∞) m 0 → TM d
 plug t m = Sem.sem (Substitution d) (pack (λ _ → t))
\end{code}
%</plug>
%<*unroll>
\begin{code}
 unroll : TM d → ⟦ d ⟧ (λ _ _ → TM d) 0
 unroll t′@(`con t) = fmap d (plug t′) t
\end{code}
%</unroll>
\begin{code}
 unroll t′@(`var ())
\end{code}
%<*unfold>
\begin{code}
 unfold : {i : Size} → TM d → ∞Tm d i
 ∞Tm.force (unfold t′) = fmap d (λ _ → unfold) (unroll t′)
\end{code}
%</unfold>
-- Simple example: Potentially cyclic lists

`listD : Set → Desc
`listD A = `∎                 -- nil
        `+ `σ A λ _ → `X 1 `∎ -- cons (includes pointer declaration)

pattern nil       = `con (true , tt) 
pattern cons x xs = `con (false , x , xs , tt)

`1∷2∷3 : Tm (`listD ℕ) ∞ 0
`1∷2∷3 = cons 1 (cons 2 (cons 3 nil))

`1∷2⇖1 : Tm (`listD ℕ) ∞ 0
`1∷2⇖1 = cons 1 (cons 2 (`var (suc zero)))

∞1∷2 : ∞Tm (`listD ℕ) ∞
∞2∷1 : ∞Tm (`listD ℕ) ∞

∞Tm.force ∞1∷2 = (false , 1 , ∞2∷1 , tt)
∞Tm.force ∞2∷1 = (false , 2 , ∞1∷2 , tt)

eq₁ : ∀ {i} → ≈^∞Tm (`listD ℕ) i ∞1∷2 (unfold `1∷2⇖1)
eq₂ : ∀ {i} → ≈^∞Tm (`listD ℕ) i ∞2∷1 (unfold (cons 2 (th^Tm `1∷2⇖1 ε)))

≈^∞Tm.force eq₁ = _≡_.refl , _≡_.refl , eq₂ , tt
≈^∞Tm.force eq₂ = _≡_.refl , _≡_.refl , eq₁ , tt
\end{code}

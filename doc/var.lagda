\begin{code}

module var where

open import indexed
open import Data.Nat

\end{code}
%<*var>
\begin{code}
data Var : ℕ → Set where
  z : [        suc ⊢ Var ]
  s : [ Var ⟶  suc ⊢ Var ]
\end{code}
%</var>

\begin{code}
injectˡ : ∀ {n} k → Var n → Var (n + k)
injectˡ k z     = z
injectˡ k (s v) = s (injectˡ k v)

injectʳ : ∀ {n} k → Var n → Var (k + n)
injectʳ zero    v = v
injectʳ (suc k) v = s (injectʳ k v)
\end{code}

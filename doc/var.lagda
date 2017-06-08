\begin{code}
-- When scopes are represented by lists of kinds, a variable of
-- a given kind is a position in such a list. This is a strongly
-- typed version of de Bruijn indices hence the name we picked
-- for Var's constructor:
-- * z for zero
-- * s for successor

module var {I : Set} where

open import indexed
open import Data.List.Base hiding ([_])

\end{code}
%<*var>
\begin{code}
data Var (i : I) : List I → Set where
  z :            [            (i ∷_) ⊢ Var i ]
  s : {j : I} →  [ Var i ⟶  (j ∷_) ⊢ Var i ]
\end{code}
%</var>

\begin{code}
injectˡ :  {i : I} (ys : List I) → [ Var i ⟶ (_++ ys) ⊢ Var i ]
injectˡ k z      = z
injectˡ k (s v)  = s (injectˡ k v)

injectʳ : {i : I} (ys : List I) → [ Var i ⟶ (ys ++_) ⊢ Var i ]
injectʳ []        v = v
injectʳ (y ∷ ys)  v = s (injectʳ ys v)
\end{code}

\begin{code}
module Generic.Semantics.Unit where

open import Data.Unit
open import var
open import Generic.Semantics

module _ {I : Set} where

 Unit : I ─Scoped
 Unit = λ _ _ → ⊤

 SemUnit : ∀ {d} → Sem d Unit Unit
 SemUnit = _
\end{code}

\begin{code}
{-# OPTIONS --safe --sized-types #-}
module Generic.Cofinite where

open import Size
open import Data.Unit
open import Data.List.Base hiding (unfold)

open import Data.Environment
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic

private
  variable
    I : Set
    s : Size

\end{code}
%<*cotm>
\begin{code}
record ∞Tm (d : Desc I) (s : Size) (i : I) : Set where
  coinductive; constructor `con
  field force :  {s' : Size< s} → ⟦ d ⟧ (λ _ i _ → ∞Tm d s' i) i []
\end{code}
%</cotm>
\begin{code}
open ∞Tm public

module _ {d : Desc ⊤} where
\end{code}
%<*plug>
\begin{code}
  plug : TM d tt → ∀ Δ i → Scope (Tm d ∞) Δ i [] → TM d i
  plug t Δ i = Semantics.semantics Substitution (pack (λ _ → t))
\end{code}
%</plug>
%<*unroll>
\begin{code}
  unroll : TM d tt → ⟦ d ⟧ (λ _ i _ → TM d i) tt []
  unroll t′@(`con t) = fmap d (plug t′) t
\end{code}
%</unroll>
%<*unfold>
\begin{code}
  unfold : TM d tt → ∞Tm d s tt
  unfold t .force = fmap d (λ _ _ → unfold) (unroll t)
\end{code}
%</unfold>

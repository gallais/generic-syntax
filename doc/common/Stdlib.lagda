\begin{code}
module Stdlib where

open import Data.Product
open import Data.List.Base

private

  variable
    A B : Set
\end{code}

%<*constant>
\begin{code}
const : Set → (A → Set)
const P x = P
\end{code}
%</constant>

%<*product>
\begin{code}
_∙×_ : (P Q : A → Set) → (A → Set)
(P ∙× Q) x = P x × Q x
\end{code}
%</product>

%<*arrow>
\begin{code}
_⇒_ : (P Q : A → Set) → (A → Set)
(P ⇒ Q) x = P x → Q x
\end{code}
%</arrow>
%<*forall>
\begin{code}
∀[_] : (A → Set) → Set
∀[_] P = ∀ {x} → P x
\end{code}
%</forall>
%<*adjust>
\begin{code}
_⊢_ : (A → B) → (B → Set) → (A → Set)
(f ⊢ P) x = P (f x)
\end{code}
%</adjust>
\begin{code}


\end{code}
%<*bottom>
\begin{code}
data ⊥ : Set where
\end{code}
%</bottom>
\begin{code}


\end{code}
%<*dec>
\begin{code}
data Dec (P : Set) : Set where
  yes  : P        → Dec P
  no   : (P → ⊥)  → Dec P
\end{code}
%</dec>
\begin{code}

\end{code}
%<*all>
\begin{code}
data All (P : A → Set) : List A → Set where
  []   : All P []
  _∷_  : ∀ {a as} → P a → All P as → All P (a ∷ as)
\end{code}
%</all>

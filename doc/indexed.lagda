\begin{code}

module indexed {I : Set} where

open import Level
open import Data.Sum using (_⊎_) public
open import Data.Product using (_×_) public
\end{code}

\AgdaHide{
\begin{code}
infixr 5 _⟶_
infixr 6 _∙⊎_
infixr 7 _∙×_
infix  8 _⊢_
\end{code}}

\begin{code}
_∙⊎_ : {ℓ ℓ′ : Level} → (I → Set ℓ) → (I → Set ℓ′) → (I → Set (ℓ′ ⊔ ℓ))
(S ∙⊎ T) i = S i ⊎ T i
\end{code}
%<*arrow>
\begin{code}
_⟶_ :  {ℓ ℓ′ : Level} → (I → Set ℓ) → (I → Set ℓ′) → (I → Set (ℓ′ ⊔ ℓ))
(S ⟶ T) i = S i → T i
\end{code}
%</arrow>
%<*constant>
\begin{code}
κ : {ℓ : Level} → Set ℓ → (I → Set ℓ)
κ S i = S
\end{code}
%</constant>
%<*forall>
\begin{code}
[_] :  {ℓ : Level} → (I → Set ℓ) → Set ℓ
[ T ] = ∀ {i} → T i
\end{code}
%</forall>
%<*product>
\begin{code}
_∙×_ :  {ℓ ℓ′ : Level} → (I → Set ℓ) → (I → Set ℓ′) → (I → Set (ℓ′ ⊔ ℓ))
(S ∙× T) i = S i × T i
\end{code}
%</product>
%<*adjust>
\begin{code}
_⊢_ :  {ℓ : Level} → (I → I) → (I → Set ℓ) → (I → Set ℓ)
(f ⊢ T) i = T (f i)
\end{code}
%</adjust>

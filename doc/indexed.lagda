\begin{code}
-- Heavily using indexed families can lead to fairly unreadable
-- types. We design this library of combinators to lighten such
-- types by only mentioning the important changes made to the
-- index: whenever the index is kept the same, the combinators
-- thread it silently, and [_] universally quantifies over it.

-- For instance:
-- [ f ⊢ S ∙⊎ T ⟶ U ∙× V ]
-- corresponds to
-- {i : I} → S (f i) ⊎ T i → U i × V i
-- (cf. test at the end of the file)

module indexed {ℓ^I} {I : Set ℓ^I} where

open import Level using (Level ; _⊔_)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_)
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
[_] :  {ℓ : Level} → (I → Set ℓ) → Set (ℓ^I ⊔ ℓ)
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

\begin{code}
open import Agda.Builtin.Equality
_ : ∀ {f : I → I} {S T U V : I → Set} →
    [ f ⊢ S ∙⊎ T ⟶ U ∙× V ] ≡ ({i : I} → S (f i) ⊎ T i → U i × V i)
_ = refl
\end{code}

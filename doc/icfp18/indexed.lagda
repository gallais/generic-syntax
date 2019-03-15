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

module indexed {ℓ′′} {A : Set ℓ′′} where

open import Level using (Level ; _⊔_)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_)
\end{code}

\AgdaHide{
\begin{code}
module OnlyForShow {A : Set} where
 infixr 5 _⟶_
 infixr 6 _∙⊎_
 infixr 7 _∙×_
 infix  8 _⊢_
\end{code}}

\begin{code}
 _∙⊎_ : (S T : A → Set) → (A → Set)
 (S ∙⊎ T) a = S a ⊎ T a
\end{code}
%<*arrow>
\begin{code}
 _⟶_ : (S T : A → Set) → (A → Set)
 (S ⟶ T) a = S a → T a
\end{code}
%</arrow>
%<*constant>
\begin{code}
 κ : Set → (A → Set)
 κ S a = S
\end{code}
%</constant>
%<*forall>
\begin{code}
 [_] : (A → Set) → Set
 [ T ] = ∀ {a} → T a
\end{code}
%</forall>
%<*product>
\begin{code}
 _∙×_ : (S T : A → Set) → (A → Set)
 (S ∙× T) a = S a × T a
\end{code}
%</product>
%<*adjust>
\begin{code}
 _⊢_ :  (A → A) → (A → Set) → (A → Set)
 (f ⊢ T) a = T (f a)
\end{code}
%</adjust>

\begin{code}
infixr 5 _⟶_
infixr 6 _∙⊎_
infixr 7 _∙×_
infix  8 _⊢_

_∙⊎_ : {ℓ ℓ′ : Level} → (A → Set ℓ) → (A → Set ℓ′) → (A → Set (ℓ′ ⊔ ℓ))
(S ∙⊎ T) a = S a ⊎ T a

_⟶_ :  {ℓ ℓ′ : Level} → (A → Set ℓ) → (A → Set ℓ′) → (A → Set (ℓ′ ⊔ ℓ))
(S ⟶ T) a = S a → T a

κ : {ℓ : Level} → Set ℓ → (A → Set ℓ)
κ S a = S

[_] :  {ℓ : Level} → (A → Set ℓ) → Set (ℓ′′ ⊔ ℓ)
[ T ] = ∀ {a} → T a

_∙×_ :  {ℓ ℓ′ : Level} → (A → Set ℓ) → (A → Set ℓ′) → (A → Set (ℓ′ ⊔ ℓ))
(S ∙× T) a = S a × T a

_⊢_ :  {ℓ : Level} → (A → A) → (A → Set ℓ) → (A → Set ℓ)
(f ⊢ T) a = T (f a)

open import Agda.Builtin.Equality
_ : ∀ {f : A → A} {S T U V : A → Set} →
    [ f ⊢ S ∙⊎ T ⟶ U ∙× V ] ≡ ({a : A} → S (f a) ⊎ T a → U a × V a)
_ = refl
\end{code}

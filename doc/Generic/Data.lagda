\begin{code}
module Generic.Data where

open import indexed
open import Size
open import Data.Bool
open import Data.Unit
open import Data.Product as Prod
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

\end{code}
%<*desc>
\begin{code}
data Desc (I J : Set) : Set₁ where
  `σ : (A : Set) (d : A → Desc I J)  →  Desc I J
  `X : J → Desc I J                  →  Desc I J
  `∎ : I                             →  Desc I J
\end{code}
%</desc>
\begin{code}
module _ {I J : Set} where
 infixr 5 _`+_

 `K : Set → I → Desc I J
 `K A i = `σ A (λ _ → `∎ i)
\end{code}

%<*sum>
\begin{code}
 _`+_ : Desc I J → Desc I J → Desc I J
 d `+ e = `σ Bool $ λ { true  → d ; false → e }
\end{code}
%</sum>

%<*interp>
\begin{code}
 ⟦_⟧ : Desc I J → (J → Set) → (I → Set)
 ⟦ `σ A d  ⟧ X i = Σ[ a ∈ A ] (⟦ d a ⟧ X i)
 ⟦ `X j d  ⟧ X i = X j × ⟦ d ⟧ X i
 ⟦ `∎ i′    ⟧ X i = i ≡ i′
\end{code}
%</interp>
%<*fmap>
\begin{code}
 fmap : {X Y : J → Set} → (d : Desc I J) → [ X ⟶ Y ] → [ ⟦ d ⟧ X ⟶ ⟦ d ⟧ Y ]
 fmap (`σ A d) f (a , v)  = (a , fmap (d a) f v)
 fmap (`X j d) f (r , v)  = (f r , fmap d f v)
 fmap (`∎ i)   f t        = t
\end{code}
%</fmap>

%<*mu>
\begin{code}
data μ {I : Set} (d : Desc I I) : Size → I → Set where
  `con : {i : I} {s : Size} → ⟦ d ⟧ (μ d s) i → μ d (↑ s) i
\end{code}
%</mu>

%<*fold>
\begin{code}
fold : {I : Set} {X : I → Set} {s : Size} → (d : Desc I I) → [ ⟦ d ⟧ X ⟶ X ] → [ μ d s ⟶ X ]
fold d alg (`con t) = alg (fmap d (fold d alg) t)
\end{code}
%</fold>

%<*listD>
\begin{code}
listD : Set → Desc ⊤ ⊤
listD A =  `σ Bool $ λ isNil →
           if isNil then `∎ tt else `σ A (λ _ → `X tt (`∎ tt))
\end{code}
%</listD>

%<*listD>
\begin{code}
List : Set → Set
List A = μ (listD A) ∞ tt
\end{code}
%</listD>

%<*nil>
\begin{code}
[] : {A : Set} → μ (listD A) ∞ tt
[] = `con (true , refl)
\end{code}
%</nil>

\begin{code}
infixr 10 _∷_
\end{code}

%<*cons>
\begin{code}
_∷_ : {A : Set} → A → List A → List A
x ∷ xs = `con (false , x , xs , refl)
\end{code}
%</cons>

%<*example>
\begin{code}
example : List (List Bool)
example  = (false ∷ []) ∷ (true ∷ []) ∷ []
\end{code}
%</example>

%<*foldr>
\begin{code}
foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr {A} {B} c n = fold (listD A) alg where

  alg : ⟦ listD A ⟧ (const B) tt → B
  alg (true             , refl)  = n
  alg (false , hd , rec , refl)  = c hd rec
\end{code}
%</foldr>

%<*append>
\begin{code}
_++_ : {A : Set} → List A  → List A → List A
_++_ = foldr (λ hd rec → hd ∷_ ∘ rec) id
\end{code}
%</append>

%<*append>
\begin{code}
flatten : {A : Set} → List (List A) → List A
flatten = foldr _++_ []
\end{code}
%</append>

%<*test>
\begin{code}
test : flatten example ≡ false ∷ true ∷ []
test = refl
\end{code}
%</test>




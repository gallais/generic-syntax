\begin{code}
{-# OPTIONS --safe --sized-types #-}

module StateOfTheArt.CDMM where

open import Size
open import Data.Empty
open import Data.Bool
open import Data.Nat using (ℕ ; suc)
open import Data.Unit
open import Data.Product as Prod
open import Function
open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])

\end{code}
%<*desc>
\begin{code}
data Desc (I J : Set) : Set₁ where
  `σ : (A : Set) → (A → Desc I J) → Desc I J
  `X : J → Desc I J → Desc I J
  `∎ : I → Desc I J
\end{code}
%</desc>
\begin{code}
private
  variable
    I J : Set
    i : I
    j : J
    d : Desc I J
    X Y : J → Set
    s : Size
    A B : Set

`K : Set → I → Desc I J
`K A i = `σ A (λ _ → `∎ i)

infixr 5 _`+_
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
⟦ `∎ i′   ⟧ X i = i ≡ i′
\end{code}
%</interp>
%<*fmap>
\begin{code}
fmap : (d : Desc I J) → ∀[ X ⇒ Y ] → ∀[ ⟦ d ⟧ X ⇒ ⟦ d ⟧ Y ]
fmap (`σ A d)  f (a , v)  = (a , fmap (d a) f v)
fmap (`X j d)  f (r , v)  = (f r , fmap d f v)
fmap (`∎ i)    f t        = t
\end{code}
%</fmap>

%<*mu>
\begin{code}
data μ (d : Desc I I) : Size → I → Set where
  `con : ⟦ d ⟧ (μ d s) i → μ d (↑ s) i
\end{code}
%</mu>

%<*fold>
\begin{code}
fold : (d : Desc I I) → ∀[ ⟦ d ⟧ X ⇒ X ] → ∀[ μ d s ⇒ X ]
fold d alg (`con t) = alg (fmap d (fold d alg) t)
\end{code}
%</fold>


%<*finD>
\begin{code}
finD : Desc ℕ ℕ
finD =  `σ ℕ $ λ index →
        `σ Bool $ λ isZero → if isZero
        then `∎ (suc index)
        else `X index (`∎ (suc index))
\end{code}
%</finD>

%<*fin>
\begin{code}
fin : ℕ → Set
fin = μ finD ∞
\end{code}
%</fin>

%<*finz-elim>
\begin{code}
fin0-elim : fin 0 → ⊥
fin0-elim (`con (_ , true , ()))
fin0-elim (`con (_ , false , _ , ()))
\end{code}
%</finz-elim>

%<*fz>
\begin{code}
fz : ∀ n → fin (suc n)
fz n = `con (n , true , refl)
\end{code}
%</fz>

%<*fs>
\begin{code}
fs : ∀ n → fin n → fin (suc n)
fs n k = `con (n , false , k , refl)
\end{code}
%</fs>

%<*listD>
\begin{code}
listD : Set → Desc ⊤ ⊤
listD A =  `σ Bool $ λ isNil →
           if isNil then `∎ tt
           else `σ A (λ _ → `X tt (`∎ tt))
\end{code}
%</listD>

%<*list>
\begin{code}
List : Set → Set
List A = μ (listD A) ∞ tt
\end{code}
%</list>

%<*nil>
\begin{code}
[] : μ (listD A) ∞ tt
[] = `con (true , refl)
\end{code}
%</nil>

\begin{code}
infixr 10 _∷_
\end{code}
%<*cons>
\begin{code}
_∷_ : A → List A → List A
x ∷ xs = `con (false , x , xs , refl)
\end{code}
%</cons>

%<*example>
\begin{code}
example : List (List Bool)
example = (false ∷ []) ∷ (true ∷ []) ∷ []
\end{code}
%</example>

%<*vecD>
\begin{code}
vecD : Set → Desc ℕ ℕ
vecD A =  `σ Bool $ λ isNil →
          if isNil then `∎ 0
          else `σ ℕ (λ n → `σ A (λ _ → `X n (`∎ (suc n))))
\end{code}
%</vecD>

%<*vec>
\begin{code}
Vec : Set → ℕ → Set
Vec A = μ (vecD A) ∞
\end{code}
%</vec>

%<*foldr>
\begin{code}
foldr : (A → B → B) → B → List A → B
foldr {A} {B} c n = fold (listD A) alg where

  alg : ⟦ listD A ⟧ (const B) tt → B
  alg (true             , refl)  = n
  alg (false , hd , rec , refl)  = c hd rec
\end{code}
%</foldr>

%<*append>
\begin{code}
_++_ : List A  → List A → List A
_++_ = foldr (λ hd rec → hd ∷_ ∘ rec) id
\end{code}
%</append>

%<*append>
\begin{code}
flatten : List (List A) → List A
flatten = foldr _++_ []
\end{code}
%</append>

%<*test>
\begin{code}
test : flatten example ≡ false ∷ true ∷ []
test = refl
\end{code}
%</test>




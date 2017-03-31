\begin{code}
module generic-data where

open import Size
open import Data.Bool
open import Data.Unit
open import Data.Product as Prod
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

\end{code}
%<*desc>
\begin{code}
data Desc : Set₁ where
  `σ : (A : Set) (d : A → Desc)  →  Desc
  `X : Desc                      →  Desc
  `∎ :                              Desc
\end{code}
%</desc>
\begin{code}
infixr 6 _`×_
infixr 5 _`+_

`K : Set → Desc
`K A = `σ A (λ _ → `∎)
\end{code}

%<*sum>
\begin{code}
_`+_ : Desc → Desc → Desc
d `+ e = `σ Bool $ λ { true  → d ; false → e }
\end{code}
%</sum>

\begin{code}
_`×_ : Desc → Desc → Desc
`σ A d  `× e = `σ A (λ a → d a `× e)
`X d    `× e = `X (d `× e)
`∎      `× e = e

\end{code}
%<*interp>
\begin{code}
⟦_⟧ : Desc → (Set → Set)
⟦ `σ A d  ⟧ X = Σ[ a ∈ A ] (⟦ d a ⟧ X)
⟦ `X d    ⟧ X = X × ⟦ d ⟧ X
⟦ `∎      ⟧ X = ⊤
\end{code}
%</interp>
%<*fmap>
\begin{code}
fmap : {X Y : Set} → (d : Desc) → (X → Y) → (⟦ d ⟧ X → ⟦ d ⟧ Y)
fmap (`σ A d) f (a , v)  = (a , fmap (d a) f v)
fmap (`X d)   f (r , v)  = (f r , fmap d f v)
fmap `∎       f t        = t
\end{code}
%</fmap>

%<*mu>
\begin{code}
data μ (d : Desc) : Size → Set where
  `con : {i : Size} → ⟦ d ⟧ (μ d i) → μ d (↑ i)
\end{code}
%</mu>

%<*fold>
\begin{code}
fold : {X : Set} {i : Size} → (d : Desc) → (⟦ d ⟧ X → X) → μ d i → X
fold d alg (`con t) = alg (fmap d (fold d alg) t)
\end{code}
%</fold>

%<*listD>
\begin{code}
listD : Set → Desc
listD A =  `σ Bool $ λ isNil →
           if isNil then `∎ else `σ A (λ _ → `X `∎)
\end{code}
%</listD>

%<*listD>
\begin{code}
[_] : Set → Set
[ A ] = μ (listD A) ∞
\end{code}
%</listD>

%<*nil>
\begin{code}
[] : {A : Set} → μ (listD A) ∞
[] = `con (true , tt)
\end{code}
%</nil>

\begin{code}
infixr 10 _∷_
\end{code}

%<*cons>
\begin{code}
_∷_ : {A : Set} → A → [ A ] → [ A ]
x ∷ xs = `con (false , x , xs , tt)
\end{code}
%</cons>

%<*example>
\begin{code}
example : [ [ Bool ] ]
example  = (false ∷ []) ∷ (true ∷ []) ∷ []
\end{code}
%</example>

%<*foldr>
\begin{code}
foldr : {A B : Set} → (A → B → B) → B → [ A ] → B
foldr {A} {B} c n = fold (listD A) alg where

  alg : ⟦ listD A ⟧ B → B
  alg (true , tt) = n
  alg (false , hd , rec , tt) = c hd rec
\end{code}
%</foldr>

%<*append>
\begin{code}
_++_ : {A : Set} → [ A ] → [ A ] → [ A ]
_++_ = foldr (λ hd rec → hd ∷_ ∘ rec) id
\end{code}
%</append>

%<*append>
\begin{code}
flatten : {A : Set} → [ [ A ] ] → [ A ]
flatten = foldr _++_ []
\end{code}
%</append>

%<*test>
\begin{code}
test : flatten example ≡ false ∷ true ∷ []
test = refl
\end{code}
%</test>




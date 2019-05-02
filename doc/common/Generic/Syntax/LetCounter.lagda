\begin{code}

{-# OPTIONS --safe --sized-types #-}

module Generic.Syntax.LetCounter where

open import Algebra
open import Algebra.Structures
open import Data.Bool
open import Data.List.Relation.Unary.All as All
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Relation.Unary
open import Function

open import Data.Var
open import Generic.Syntax

open import Generic.Syntax.LetBinder using (Let)

module _ {a} {A : Set a} (expensive : A) where

-- inlining is hard

  _ : A × A
  -- here we better not inline x (but it's fine to inline y)
\end{code}
%<*expensive>
\begin{code}
  _ =  let x = expensive  in
       let y = (x , x)    in
       y
\end{code}
%</expensive>
\begin{code}
  _ : A
  -- here on the other hand we can inline all the lets!
\end{code}
%<*cheap>
\begin{code}
  _ =  let x = expensive  in
       let y = (x , x)    in
       x
\end{code}
%</cheap>

%<*counter>
\begin{code}
data Counter : Set where
  zero  : Counter
  one   : Counter
  many  : Counter
\end{code}
%</counter>
%<*addition>
\begin{code}
_+_ : Counter → Counter → Counter
zero  + n     = n
m     + zero  = m
_     + _     = many
\end{code}
%</addition>

%<*multiplication>
\begin{code}
_*_ : Counter → Counter → Counter
zero  * n     = zero
m     * zero  = zero
one   * n     = n
m     * one   = m
many  * many  = many
\end{code}
%</multiplication>

\begin{code}

module _ {I : Set} where

  private
    variable
      σ : I

\end{code}
%<*count>
\begin{code}
  Count : List I → Set
  Count = All (const Counter)
\end{code}
%</count>
%<*zeros>
\begin{code}
  zeros : ∀[ Count ]
  zeros {[]}     = []
  zeros {σ ∷ Γ}  = zero ∷ zeros
\end{code}
%</zeros>
%<*fromVar>
\begin{code}
  fromVar : ∀[ Var σ ⇒ Count ]
  fromVar z      = one ∷ zeros
  fromVar (s v)  = zero ∷ fromVar v
\end{code}
%</fromVar>
\begin{code}

\end{code}
%<*merge>
\begin{code}
  merge : ∀[ Count ⇒ Count ⇒ Count ]
  merge []        []        = []
  merge (m ∷ cs)  (n ∷ ds)  =
    (m + n) ∷ merge cs ds
\end{code}
%</merge>
\begin{code}

\end{code}
%<*control>
\begin{code}
  control : Counter → ∀[ Count ⇒ Count ]
  control zero  cs = zeros
  control one   cs = cs -- inlined
  control many  cs = cs -- not inlined
\end{code}
%</control>
\begin{code}

\end{code}
%<*scale>
\begin{code}
  scale : Counter → ∀[ Count ⇒ Count ]
  scale zero  cs = zeros
  scale one   cs = cs
  scale k     cs = map (k *_) cs
\end{code}
%</scale>
\begin{code}


  rawMonoid : List I → RawMonoid _ _
  rawMonoid Γ = record
    { Carrier = Count Γ
    ; _≈_     = _≡_
    ; _∙_     = merge
    ; ε       = tabulate (λ _ → zero)
    }

\end{code}
%<*clet>
\begin{code}
  CLet : Desc I
  CLet = `σ Counter $ λ _ → Let
\end{code}
%</clet>
\begin{code}


pattern `IN' e t = (_ , e , t , refl)
pattern `IN  e t = `con (`IN' e t)

module _ {I : Set} {d : Desc I} where

  embed : ∀ {i σ} → ∀[ Tm d i σ ⇒ Tm (d `+ CLet) i σ ]
  embed = map^Tm (MkDescMorphism (true ,_))

\end{code}

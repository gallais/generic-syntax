\begin{code}
module Generic.Examples.TypeCheckin where

open import Size
open import Function
open import Data.Unit
open import Data.Bool
open import Data.Product as P hiding (,_)
open import Data.List hiding ([_])
open import Data.Maybe as Maybe hiding (All)


open import indexed
open import var hiding (_<$>_)
open import environment hiding (refl ; _<$>_ ; _>>_)
open import Generic.Syntax
open import Generic.Semantics

import Category.Monad as CM
import Level
module M = CM.RawMonad (Maybe.monad {Level.zero})
open M

open import Relation.Binary.PropositionalEquality hiding ([_])

infixr 5 _⇒_
data Type : Set where
  α    : Type
  _⇒_  : Type → Type → Type

infix 3 _==_
_==_ : (σ τ : Type) → Maybe ⊤
α     == α       = just tt
σ ⇒ τ == σ' ⇒ τ' = (σ == σ') >> (τ == τ')
_     == _       = nothing

isArrow : (σ⇒τ : Type) → Maybe (Type × Type)
isArrow (σ ⇒ τ) = just (σ , τ)
isArrow _       = nothing
\end{code}
%<*bidirectional>
\begin{code}
data Phase : Set where Check Infer : Phase

Lang : Desc Phase
Lang  =   `X [] Infer (`X [] Check (`∎ Infer))    -- apply
      `+  `X (Infer ∷ []) Check (`∎ Check)        -- lamda
      `+  `σ Type (λ _ → `X [] Check (`∎ Infer))  -- cut
      `+  `X [] Infer (`∎ Check)                  -- embed
\end{code}
%</bidirectional>
%<*langsyntax>
\begin{code}
pattern `app f t  = `con (true , f , t , refl)
pattern `lam b    = `con (false , true , b , refl)
pattern `cut σ t  = `con (false , false , true , σ , t , refl)
pattern `emb t    = `con (false , false , false , t , refl)
\end{code}
%</langsyntax>
%<*typemode>
\begin{code}
Type- : Phase → Set
Type- Check  = Type →  Maybe ⊤
Type- Infer  =         Maybe Type

Var- : Phase → Set
Var- _ = Type
\end{code}
%</typemode>
%<*typecheck>
\begin{code}
Typecheck : Sem Lang (const ∘ Var-) (const ∘ Type-)
Typecheck = record
  { th^𝓥  = λ v ρ → v
  ; var    = λ { {Infer} → just ; {Check} → _==_ }
  ; alg    = case app $ case lam $ case cut emb }
\end{code}
%</typecheck>
\begin{code}
  where

   app : {i : Phase} → Type- Infer × Type- Check × i ≡ Infer → Type- i
   app (f , t , refl) =  f            >>= λ σ⇒τ →
                         isArrow σ⇒τ  >>= uncurry λ σ τ →
                         τ <$ t σ

   lam : {i : Phase} → [ □ ((Infer ∷ [] ─Env) _ ⟶ κ (Type- Check)) ∙× κ (i ≡ Check) ⟶ κ (Type- i) ]
   lam (b , refl) σ⇒τ =  isArrow σ⇒τ >>= uncurry λ σ τ →
                         b (extend {σ = Infer}) (ε ∙ σ) τ

   cut : {i : Phase} → Type × Type- Check × i ≡ Infer → Type- i
   cut (σ , t , refl) = σ <$ t σ

   emb : {i : Phase} → Type- Infer × i ≡ Check → Type- i
   emb (t , refl) σ =  t >>= λ τ  →
                       σ == τ
\end{code}
\begin{code}
type- : (p : Phase) → Tm Lang ∞ p [] → Type- p
type- p t = Sem.sem Typecheck {Δ = []} ε t

_ : let  id  : Tm Lang ∞ Check []
         id  = `lam (`emb (`var z))
    in type- Infer (`app (`cut ((α ⇒ α) ⇒ (α ⇒ α)) id) id)
     ≡ just (α ⇒ α)
_ = refl
\end{code}

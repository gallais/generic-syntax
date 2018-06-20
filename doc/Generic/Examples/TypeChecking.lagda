\begin{code}
module Generic.Examples.TypeChecking where

open import Size
open import Function
open import Data.Unit
open import Data.Bool
open import Data.Product as P hiding (,_)
open import Data.List hiding ([_])
open import Data.Maybe as Maybe hiding (All)


open import indexed
open import var hiding (_<$>_)
open import environment hiding (_<$>_ ; _>>_)
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
%<*constructors>
\begin{code}
data LangC : Set where
  App Lam Emb : LangC
  Cut : Type → LangC
\end{code}
%</constructors>
%<*phase>
\begin{code}
data Mode : Set where
  Check Infer : Mode
\end{code}
%</phase>
%<*bidirectional>
\begin{code}
Lang : Desc Mode
Lang  =  `σ LangC $ λ where
  App      → `X [] Infer (`X [] Check (`∎ Infer))
  Lam      → `X (Infer ∷ []) Check (`∎ Check)
  (Cut σ)  → `X [] Check (`∎ Infer)
  Emb      → `X [] Infer (`∎ Check)
\end{code}
%</bidirectional>
%<*langsyntax>
\begin{code}
pattern `app f t  = `con (App , f , t , refl)
pattern `lam b    = `con (Lam , b , refl)
pattern `cut σ t  = `con (Cut σ , t , refl)
pattern `emb t    = `con (Emb , t , refl)
\end{code}
%</langsyntax>
%<*typemode>
\begin{code}
Type- : Mode → Set
Type- Check  = Type →  Maybe ⊤
Type- Infer  =         Maybe Type
\end{code}
%</typemode>
%<*varmode>
\begin{code}
Var- : Mode → Set
Var- _ = Type
\end{code}
%</varmode>
%<*typecheck>
\begin{code}
Typecheck : Sem Lang (const ∘ Var-) (const ∘ Type-)
Typecheck = record { th^𝓥 = λ v ρ → v; var = var _; alg = alg } where

   var : (i : Mode) → Var- i → Type- i
   var Infer  = just
   var Check  = _==_

   alg : {i : Mode} {Γ : List Mode} → ⟦ Lang ⟧ (Kripke (κ ∘ Var-) (κ ∘ Type-)) i Γ → Type- i
   alg (App , f , t , refl)  =  f            >>= λ σ⇒τ →
                                isArrow σ⇒τ  >>= uncurry λ σ τ →
                                τ <$ t σ
   alg (Lam , b , refl)      =  λ σ⇒τ → isArrow σ⇒τ >>= uncurry λ σ τ →
                                b (extend {σ = Infer}) (ε ∙ σ) τ
   alg (Cut σ , t , refl)    =  σ <$ t σ
   alg (Emb , t , refl)      =  λ σ → t >>= λ τ → σ == τ
\end{code}
%</typecheck>
\begin{code}
type- : (p : Mode) → Tm Lang ∞ p [] → Type- p
type- p t = Sem.sem Typecheck {Δ = []} ε t

_ : let  id  : Tm Lang ∞ Check []
         id  = `lam (`emb (`var z))
    in type- Infer (`app (`cut ((α ⇒ α) ⇒ (α ⇒ α)) id) id)
     ≡ just (α ⇒ α)
_ = refl
\end{code}

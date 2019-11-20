\begin{code}
{-# OPTIONS --safe --sized-types #-}

module StateOfTheArt.ACMM where

open import Data.Var hiding (_<$>_; get)
open import Data.Environment as E hiding (_>>_ ; extend)

open import Data.Nat.Base
open import Data.List.Base using (List; _∷_; [])
open import Function
open import Relation.Unary

private
  variable
    I : Set

infixr 3 _`→_
\end{code}
%<*type>
\begin{code}
data Type : Set where
  α     : Type
  _`→_  : Type → Type → Type
\end{code}
%</type>
\begin{code}
private
  variable
    σ τ : I
    Γ Δ Θ : List I
    A B : Set

\end{code}
%<*tm>
\begin{code}
data Lam : Type ─Scoped where
  `var  : ∀[ Var σ ⇒ Lam σ ]
  `app  : ∀[ Lam (σ `→ τ) ⇒ Lam σ ⇒ Lam τ ]
  `lam  : ∀[ (σ ∷_) ⊢ Lam τ ⇒ Lam (σ `→ τ) ]
\end{code}
%</tm>
\begin{code}
module Renaming where

 varᵣ : ∀[ Var σ ⇒ Lam σ ]
 varᵣ = `var

 extendᵣ : (Γ ─Env) Var Δ → (σ ∷ Γ ─Env) Var (σ ∷ Δ)
 extendᵣ ρ = s <$> ρ ∙ z
\end{code}
%<*ren>
\begin{code}
 ren : (Γ ─Env) Var Δ → Lam σ Γ → Lam σ Δ
 ren ρ (`var k)    = varᵣ (lookup ρ k)
 ren ρ (`app f t)  = `app (ren ρ f) (ren ρ t)
 ren ρ (`lam b)    = `lam (ren (extendᵣ ρ) b)
\end{code}
%</ren>
\begin{code}
module Substitution where
 extendₛ : (Γ ─Env) Lam Δ → (σ ∷ Γ ─Env) Lam (σ ∷ Δ)
 extendₛ ρ = Renaming.ren E.extend <$> ρ ∙ `var z

 varₛ : ∀[ Lam σ ⇒ Lam σ ]
 varₛ x = x
\end{code}
%<*sub>
\begin{code}
 sub : (Γ ─Env) Lam Δ → Lam σ Γ → Lam σ Δ
 sub ρ (`var k)    = varₛ (lookup ρ k)
 sub ρ (`app f t)  = `app (sub ρ f) (sub ρ t)
 sub ρ (`lam b)    = `lam (sub (extendₛ ρ) b)
\end{code}
%</sub>
\begin{code}
module _ where

 private
   Val : Type ─Scoped
   Val α       = Lam α
   Val (σ `→ τ) = □ (Val σ ⇒ Val τ)

   th^Val : (σ : Type) → Thinnable (Val σ)
   th^Val α       = λ ρ t → Renaming.ren t ρ
   th^Val (σ `→ τ) = th^□

   reify   : (σ : Type) → ∀[ Val σ ⇒ Lam σ ]
   reflect : (σ : Type) → ∀[ Lam σ ⇒ Val σ ]

   reify   α = id
   reify   (σ `→ τ) = λ b → `lam (reify τ (b E.extend (reflect σ (`var z))))

   reflect α = id
   reflect (σ `→ τ) = λ b ρ v → reflect τ (`app (Renaming.ren ρ b) (reify σ v))

   extendₙ : Thinning Δ Θ → (Γ ─Env) Val Δ → Val σ Θ → (σ ∷ Γ ─Env) Val Θ
   extendₙ r ρ v = (λ {σ} v → th^Val σ v r) <$> ρ ∙ v

   varₙ : Var σ Γ → ∀[ Val σ ⇒ Val σ ]
   varₙ _ x = x

   appₙ : Lam (σ `→ τ) Γ → ∀[ Val (σ `→ τ) ⇒ Val σ ⇒ Val τ ]
   appₙ _ f t = f (pack id) t
\end{code}
%<*nbe>
\begin{code}
 nbe : (Γ ─Env) Val Δ → Lam σ Γ → Val σ Δ
 nbe ρ (`var k)    = varₙ k (lookup ρ k)
 nbe ρ (`app f t)  = appₙ f (nbe ρ f) (nbe ρ t)
 nbe ρ (`lam b)    = λ σ v → nbe (extendₙ σ ρ v) b
\end{code}
%</nbe>

%<*rsem>
\begin{AgdaAlign}
\AgdaNoSpaceAroundCode
\begin{AgdaSuppressSpace}
%<*rsemtype>
\begin{code}
record Semantics (𝓥 𝓒 : Type ─Scoped) : Set where
\end{code}
%</rsemtype>
\begin{code}
  field
\end{code}
%<*thV>
\begin{code}
    th^𝓥  : Thinnable (𝓥 σ)
\end{code}
%</thV>
%<*var>
\begin{code}
    var   : ∀[ 𝓥 σ ⇒ 𝓒 σ ]
\end{code}
%</var>
%<*app>
\begin{code}
    app   : ∀[ 𝓒 (σ `→ τ) ⇒ 𝓒 σ ⇒ 𝓒 τ ]
\end{code}
%</app>
%<*lam>
\begin{code}
    lam   : ∀[ □ (𝓥 σ ⇒ 𝓒 τ) ⇒ 𝓒 (σ `→ τ) ]
\end{code}
%</lam>
\end{AgdaSuppressSpace}
\AgdaSpaceAroundCode
\end{AgdaAlign}
%</rsem>
%<*extend>
\begin{code}
  extend : Thinning Δ Θ → (Γ ─Env) 𝓥 Δ → 𝓥 σ Θ → ((σ ∷ Γ) ─Env) 𝓥 Θ
  extend σ ρ v = ((λ t → th^𝓥 t σ) <$> ρ) ∙ v
\end{code}
%</extend>
%<*sem>
\begin{AgdaAlign}
\AgdaNoSpaceAroundCode
%<*semtype>
\begin{code}
  semantics : (Γ ─Env) 𝓥 Δ → (Lam σ Γ → 𝓒 σ Δ)
\end{code}
%</semtype>
\begin{AgdaSuppressSpace}
\begin{code}
  semantics ρ (`var k)    = var (lookup ρ k)
  semantics ρ (`app f t)  = app (semantics ρ f) (semantics ρ t)
  semantics ρ (`lam b)    = lam (λ σ v → semantics (extend σ ρ v) b)
\end{code}
\end{AgdaSuppressSpace}
\AgdaSpaceAroundCode
\end{AgdaAlign}
%</sem>

\begin{code}
open E using (extend)
\end{code}

%<*semren>
\begin{code}
Renaming : Semantics Var Lam
Renaming = record
  { th^𝓥  = th^Var
  ; var   = `var
  ; app   = `app
  ; lam   = λ b → `lam (b extend z) }
\end{code}
%</semren>
%<*semrenfun>
\begin{code}
ren : (Γ ─Env) Var Δ → Lam σ Γ → Lam σ Δ
ren = Semantics.semantics Renaming
\end{code}
%</semrenfun>
%<*semsub>
\begin{code}
Substitution : Semantics Lam Lam
Substitution = record
   { th^𝓥  = λ t ρ → ren ρ t
   ; var   = id
   ; app   = `app
   ; lam   = λ b → `lam (b extend (`var z)) }
\end{code}
%</semsub>
%<*semsubfun>
\begin{code}
sub : (Γ ─Env) Lam Δ → Lam σ Γ → Lam σ Δ
sub = Semantics.semantics Substitution
\end{code}
%</semsubfun>

\begin{code}
open import Category.Monad.State
open import Category.Applicative
open import Data.String hiding (show)
open import Data.Nat.Show
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

module Printer where
 open import Codata.Stream as Stream using (Stream; _∷_; head; tail)
 open RawMonadState (StateMonadState (Stream String _))
\end{code}
%<*monad>
\begin{code}
 Fresh : Set → Set
 Fresh = State (Stream String _)
\end{code}
%</monad>
%<*valprint>
\begin{code}
 record Wrap (A : Set) (σ : I) (Γ : List I) : Set where
   constructor MkW; field getW : A
\end{code}
%</valprint>
\begin{code}
 open Wrap public
\end{code}
%<*name>
\begin{code}
 Name : I ─Scoped
 Name = Wrap String
\end{code}
%</name>
%<*printer>
\begin{code}
 Printer : I ─Scoped
 Printer = Wrap (Fresh String)
\end{code}
%</printer>
\begin{code}

 th^Wrap : Thinnable {I} (Wrap A σ)
 th^Wrap w ρ = MkW (getW w)

 map^Wrap : (A → B) → ∀[ Wrap A σ ⇒ Wrap B σ ]
 map^Wrap f (MkW a) = MkW (f a)

 open E hiding (_>>_)
\end{code}
%<*freshprint>
\begin{code}
 fresh : ∀ σ → Fresh (Name σ (σ ∷ Γ))
 fresh σ = do
   names ← get
   put (tail names)
   pure (MkW (head names))
\end{code}
%</freshprint>
%<*semprint>
\begin{code}
 Printing : Semantics Name Printer
 Printing = record { th^𝓥 = th^Wrap; var = var; app = app; lam = lam }
\end{code}
%</semprint>
\begin{code}
  where
\end{code}
%<*printvar>
\begin{code}
   var : ∀[ Name σ ⇒ Printer σ ]
   var = map^Wrap return
\end{code}
%</printvar>
%<*printapp>
\begin{code}
   app : ∀[ Printer (σ `→ τ) ⇒ Printer σ ⇒ Printer τ ]
   app mf mt = MkW do
     f ← getW mf
     t ← getW mt
     return (f ++ " (" ++ t ++ ")")
\end{code}
%</printapp>
%<*printlam>
\begin{code}
   lam : ∀[ □ (Name σ ⇒ Printer τ) ⇒ Printer (σ `→ τ) ]
   lam {σ} mb = MkW do
     x ← fresh σ
     b ← getW (mb extend x)
     return ("λ" ++ getW x ++ ". " ++ b)
\end{code}
%</printlam>
\begin{code}

 open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
 open import Codata.Thunk using (force)
 import Data.Nat.Show as NatShow

 alphabetWithSuffix : String → List⁺ String
 alphabetWithSuffix suffix = List⁺.map (λ c → fromList (c ∷ []) ++ suffix)
                           $′ 'a' ∷ toList "bcdefghijklmnopqrstuvwxyz"

 allNats : Stream ℕ _
 allNats = Stream.iterate suc 0

 names : Stream String _
 names = Stream.concat
       $′ Stream.map alphabetWithSuffix
       $′ "" ∷ λ where .force → Stream.map NatShow.show allNats

open Printer using (getW; Printing; Name; names)
open Semantics
\end{code}

%<*print>
\begin{code}
print : Lam σ [] → String
print t = proj₁ (getW printer names) where

  empty : ([] ─Env) Name []
  empty = ε

  printer = semantics Printing empty t
\end{code}
%</print>
\begin{code}
_ : print {α `→ α} (`lam (`var z)) ≡ "λa. a"
_ = refl

module Fig1 {σ τ : Type} where

\end{code}
%<*apply>
\begin{code}
  apply : Lam ((σ `→ τ) `→ (σ `→ τ)) []
  apply =  `lam {- f -} (`lam {- x -}
           (`app (`var (s z) {- f -}) (`var z {- x -})))
\end{code}
%</apply>
\begin{code}
module Print {σ τ : Type} where

\end{code}
%<*applyprint>
\begin{code}
  apply : Lam ((σ `→ τ) `→ (σ `→ τ)) []
  apply = `lam (`lam (`app (`var (s z)) (`var z)))

  _ : print apply ≡ "λa. λb. a (b)"
  _ = refl
\end{code}
%</applyprint>
\begin{code}

_ : print {(α `→ α) `→ (α `→ α)}
          (`lam (`lam (`app (`var (s z)) (`app (`var (s z)) (`var z)))))
  ≡ "λa. λb. a (a (b))"
_ = refl
\end{code}


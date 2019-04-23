\begin{code}
{-# OPTIONS --safe --sized-types #-}

module motivation where

open import Data.Var hiding (_<$>_; get)
open import Data.Environment as E hiding (_>>_ ; extend)

open import Data.Nat.Base
open import Data.List.Base hiding ([_] ; _++_; lookup)
open import Function
open import Relation.Unary

infixr 3 _`→_
\end{code}
%<*type>
\begin{code}
data Type : Set where
  α    : Type
  _`→_  : Type → Type → Type
\end{code}
%</type>
\begin{code}
private
  variable
    σ τ : Type
    Γ Δ Θ : List Type
    A B : Set

\end{code}
%<*tm>
\begin{code}
data Lam : Type ─Scoped where
  `var : ∀[ Var σ ⇒ Lam σ ]
  `app : ∀[ Lam (σ `→ τ) ⇒ Lam σ ⇒ Lam τ ]
  `lam : ∀[ (σ ∷_) ⊢ Lam τ ⇒ Lam (σ `→ τ) ]
\end{code}
%</tm>
\begin{code}
module Renaming where

 ⟦V⟧‿ren : ∀[ Var σ ⇒ Lam σ ]
 ⟦V⟧‿ren = `var

 extend‿ren : (Γ ─Env) Var Δ → (σ ∷ Γ ─Env) Var (σ ∷ Δ)
 extend‿ren ρ = s <$> ρ ∙ z
\end{code}
%<*ren>
\begin{code}
 ren : (Γ ─Env) Var Δ → Lam σ Γ → Lam σ Δ
 ren ρ (`var k)    = ⟦V⟧‿ren (lookup ρ k)
 ren ρ (`app f t)  = `app (ren ρ f) (ren ρ t)
 ren ρ (`lam b)    = `lam (ren (extend‿ren ρ) b)
\end{code}
%</ren>
\begin{code}
module Substitution where
 extend‿sub : (Γ ─Env) Lam Δ → (σ ∷ Γ ─Env) Lam (σ ∷ Δ)
 extend‿sub ρ = Renaming.ren E.extend <$> ρ ∙ `var z

 ⟦V⟧‿sub : ∀[ Lam σ ⇒ Lam σ ]
 ⟦V⟧‿sub x = x
\end{code}
%<*sub>
\begin{code}
 sub : (Γ ─Env) Lam Δ → Lam σ Γ → Lam σ Δ
 sub ρ (`var k)    = ⟦V⟧‿sub (lookup ρ k)
 sub ρ (`app f t)  = `app (sub ρ f) (sub ρ t)
 sub ρ (`lam b)    = `lam (sub (extend‿sub ρ) b)
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

   extend : Thinning Δ Θ → (Γ ─Env) Val Δ → Val σ Θ → (σ ∷ Γ ─Env) Val Θ
   extend r ρ v = (λ {σ} v → th^Val σ v r) <$> ρ ∙ v

   ⟦V⟧ : Var σ Γ → ∀[ Val σ ⇒ Val σ ]
   ⟦V⟧ _ x = x

   ⟦A⟧ : Lam (σ `→ τ) Γ → ∀[ Val (σ `→ τ) ⇒ Val σ ⇒ Val τ ]
   ⟦A⟧ _ f t = f (pack id) t
\end{code}
%<*nbe>
\begin{code}
 nbe : (Γ ─Env) Val Δ → Lam σ Γ → Val σ Δ
 nbe ρ (`var k)    = ⟦V⟧ k (lookup ρ k)
 nbe ρ (`app f t)  = ⟦A⟧ f (nbe ρ f) (nbe ρ t)
 nbe ρ (`lam b)    = λ σ v → nbe (extend σ ρ v) b
\end{code}
%</nbe>

%<*rsem>
\begin{code}
record Sem (𝓥 𝓒 : Type ─Scoped) : Set where
  field  th^𝓥  : Thinnable (𝓥 σ)
         ⟦V⟧   : ∀[ 𝓥 σ ⇒ 𝓒 σ ]
         ⟦A⟧   : ∀[ 𝓒 (σ `→ τ) ⇒ 𝓒 σ ⇒ 𝓒 τ ]
         ⟦L⟧   : ∀[ □ (𝓥 σ ⇒ 𝓒 τ) ⇒ 𝓒 (σ `→ τ) ]
\end{code}
%</rsem>

%<*sem>
\begin{code}
  sem : (Γ ─Env) 𝓥 Δ → (Lam σ Γ → 𝓒 σ Δ)
  sem ρ (`var k)    = ⟦V⟧ (lookup ρ k)
  sem ρ (`app f t)  = ⟦A⟧ (sem ρ f) (sem ρ t)
  sem ρ (`lam b)    = ⟦L⟧ (λ σ v → sem (extend σ ρ v) b)
\end{code}
%</sem>
\begin{code}
   where

   extend : Thinning Δ Θ → (Γ ─Env) 𝓥 Δ → 𝓥 σ Θ → (σ ∷ Γ ─Env) 𝓥 Θ
   extend σ ρ v = (λ t → th^𝓥 t σ) <$> ρ ∙ v
\end{code}

%<*semren>
\begin{code}
Renaming : Sem Var Lam
Renaming = record
  { th^𝓥  = th^Var
  ; ⟦V⟧   = `var
  ; ⟦A⟧   = `app
  ; ⟦L⟧   = λ b → `lam (b (pack s) z) }
\end{code}
%</semren>
%<*semrenfun>
\begin{code}
ren : (Γ ─Env) Var Δ → Lam σ Γ → Lam σ Δ
ren = Sem.sem Renaming
\end{code}
%</semrenfun>
%<*semsub>
\begin{code}
Substitution : Sem Lam Lam
Substitution = record
   { th^𝓥  = λ t ρ → ren ρ t
   ; ⟦V⟧   = id
   ; ⟦A⟧   = `app
   ; ⟦L⟧   = λ b → `lam (b (pack s) (`var z)) }
\end{code}
%</semsub>
%<*semsubfun>
\begin{code}
sub : (Γ ─Env) Lam Δ → Lam σ Γ → Lam σ Δ
sub = Sem.sem Substitution
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
 open RawMonadState (StateMonadState ℕ)

\end{code}

%<*valprint>
\begin{code}
 record Wrap (A : Set) (σ : Type) (Γ : List Type) : Set where
   constructor MkW; field getW : A
\end{code}
%</valprint>
\begin{code}
 open Wrap public

 th^Wrap : Thinnable (Wrap A σ)
 th^Wrap w ρ = MkW (getW w)

 map^Wrap : (A → B) → ∀[ Wrap A σ ⇒ Wrap B σ ]
 map^Wrap f (MkW a) = MkW (f a)

 open E hiding (_>>_)
\end{code}
%<*freshprint>
\begin{code}
 fresh : ∀ σ → State ℕ (Wrap String σ (σ ∷ Γ))
 fresh σ = get >>= λ x → put (suc x) >> return (MkW (show x))
\end{code}
%</freshprint>
%<*semprint>
\begin{code}
 Printing : Sem (Wrap String) (Wrap (State ℕ String))
 Printing = record
   { th^𝓥  =  th^Wrap
   ; ⟦V⟧   =  map^Wrap return
   ; ⟦A⟧   =  λ mf mt → MkW $ getW mf >>= λ f → getW mt >>= λ t →
              return $ f ++ "(" ++ t ++ ")"
   ; ⟦L⟧   =  λ {σ} mb → MkW $ fresh σ >>= λ x →
              getW (mb extend x) >>= λ b →
              return $ "λ" ++ getW x ++ "." ++ b }
\end{code}
%</semprint>
\begin{code}
open Printer using (Printing)
\end{code}


\begin{code}
print : (σ : Type) → Lam σ [] → String
print _ t = proj₁ $ Printer.getW (Sem.sem Printing {Δ = []} (pack λ ()) t) 0

_ : print (α `→ α) (`lam (`var z)) ≡ "λ0.0"
_ = refl

_ : print ((α `→ α) `→ (α `→ α)) (`lam (`lam (`app (`var (s z)) (`app (`var (s z)) (`var z))))) ≡ "λ0.λ1.0(0(1))"
_ = refl
\end{code}


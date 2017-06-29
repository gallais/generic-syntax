\begin{code}
module motivation where

open import indexed
open import var hiding (_<$>_ ; get)
open import environment as E hiding (_>>_ ; refl ; extend)

open import Data.Nat.Base
open import Data.List.Base hiding ([_] ; _++_)
open import Function

infixr 3 _⇒_
\end{code}
%<*type>
\begin{code}
data Type : Set where
  α    : Type
  _⇒_  : Type → Type → Type
\end{code}
%</type>
%<*tm>
\begin{code}
data Lam : Type ─Scoped where
  V : {σ : Type} →    [ Var σ                ⟶ Lam σ        ]
  A : {σ τ : Type} →  [ Lam (σ ⇒ τ) ⟶ Lam σ  ⟶ Lam τ        ]
  L : {σ τ : Type} →  [ (σ ∷_) ⊢ Lam τ       ⟶ Lam (σ ⇒ τ)  ]
\end{code}
%</tm>
\begin{code}

module _ where

 private

   ⟦V⟧ : ∀ {n} → [ Var n ⟶ Lam n ]
   ⟦V⟧ = V

   extend : {Γ Δ : List Type} {σ : Type} → (Γ ─Env) Var Δ → (σ ∷ Γ ─Env) Var (σ ∷ Δ)
   extend ρ = s <$> ρ ∙ z
\end{code}
%<*ren>
\begin{code}
 ren : {Γ Δ : List Type} {σ : Type} → (Γ ─Env) Var Δ → Lam σ Γ → Lam σ Δ
 ren ρ (V k)    = ⟦V⟧ (lookup ρ k)
 ren ρ (A f t)  = A (ren ρ f) (ren ρ t)
 ren ρ (L b)    = L (ren (extend ρ) b)
\end{code}
%</ren>
\begin{code}
module _ where

 private
   
   extend : {Γ Δ : List Type} {σ : Type} → (Γ ─Env) Lam Δ → (σ ∷ Γ ─Env) Lam (σ ∷ Δ)
   extend ρ = ren E.extend <$> ρ ∙ V z

   ⟦V⟧ : ∀ {n} → [ Lam n ⟶ Lam n ]
   ⟦V⟧ x = x
\end{code}
%<*sub>
\begin{code}
 sub : {Γ Δ : List Type} {σ : Type} → (Γ ─Env) Lam Δ → Lam σ Γ → Lam σ Δ
 sub ρ (V k)    = ⟦V⟧ (lookup ρ k)
 sub ρ (A f t)  = A (sub ρ f) (sub ρ t)
 sub ρ (L b)    = L (sub (extend ρ) b)
\end{code}
%</sub>

\begin{code}
open import environment hiding (extend ; _>>_ ; refl)
\end{code}

%<*rsem>
\begin{code}
record Sem (𝓥 𝓒 : Type ─Scoped) : Set where
  field  th^𝓥 : {σ : Type} → Thinnable (𝓥 σ)
         ⟦V⟧   : {σ : Type} → [ 𝓥 σ         ⟶ 𝓒 σ ]
         ⟦A⟧   : {σ τ : Type} → [ 𝓒 (σ ⇒ τ) ⟶ 𝓒 σ     ⟶ 𝓒 τ ]
         ⟦L⟧   : {σ τ : Type} →  [ □ (𝓥 σ ⟶ 𝓒 τ)  ⟶ 𝓒 (σ ⇒ τ) ]
\end{code}
%</rsem>

\begin{code}
module _ {𝓥 𝓒} (𝓢 : Sem 𝓥 𝓒) where
 open Sem 𝓢
\end{code}

%<*sem>
\begin{code}
 sem : {Γ Δ : List Type} {σ : Type} → (Γ ─Env) 𝓥 Δ → (Lam σ Γ → 𝓒 σ Δ)
 sem ρ (V k)    = ⟦V⟧ (lookup ρ k)
 sem ρ (A f t)  = ⟦A⟧ (sem ρ f) (sem ρ t)
 sem ρ (L b)    = ⟦L⟧ (λ σ v → sem (extend σ ρ v) b)
\end{code}
%</sem>
\begin{code}
   where

   extend : {Γ Δ Θ : List Type} {σ : Type} →
            Thinning Δ Θ → (Γ ─Env) 𝓥 Δ → 𝓥 σ Θ → (σ ∷ Γ ─Env) 𝓥 Θ
   extend σ ρ v = (λ t → th^𝓥 t σ) <$> ρ ∙ v
\end{code}

%<*semren>
\begin{code}
Renaming : Sem Var Lam
Renaming = record
  { th^𝓥  = th^Var
  ; ⟦V⟧    = V
  ; ⟦A⟧    = A
  ; ⟦L⟧    = λ b → L (b (pack s) z) }
\end{code}
%</semren>
%<*semsub>
\begin{code}
Substitution : Sem Lam Lam
Substitution = record
   { th^𝓥  = λ t ρ → sem Renaming ρ t
   ; ⟦V⟧    = id
   ; ⟦A⟧    = A
   ; ⟦L⟧    = λ b → L (b (pack s) (V z)) }
\end{code}
%</semsub>

\begin{code}
open import Category.Monad.State
open import Category.Applicative
open import Data.String hiding (show)
open import Data.Nat.Show
open import Data.Product
open import Relation.Binary.PropositionalEquality
\end{code}

%<*semprint>
\begin{code}
Printing : Sem (λ _ _ → String) (λ _ _ → State ℕ String)
Printing = record
   { th^𝓥  = λ t _ → t
   ; ⟦V⟧    = return
   ; ⟦A⟧    =  λ mf mt → mf >>= λ f → mt >>= λ t →
               return $ f ++ "(" ++ t ++ ")"
   ; ⟦L⟧    =  λ {σ} mb → get >>= λ x → put (suc x) >>
               let x' = show x in mb (pack (s {j = σ})) x' >>= λ b →
               return $ "λ" ++ x' ++ "." ++ b }
\end{code}
%</semprint>
\begin{code}
  where open RawMonadState (StateMonadState ℕ)
\end{code}


\begin{code}
print : (σ : Type) → Lam σ [] → String
print _ t = proj₁ $ sem Printing {Δ = []} (pack λ ()) t 0

_ : print (α ⇒ α) (L (V z)) ≡ "λ0.0"
_ = refl

_ : print ((α ⇒ α) ⇒ (α ⇒ α)) (L (L (A (V (s z)) (A (V (s z)) (V z))))) ≡ "λ0.λ1.0(0(1))"
_ = refl
\end{code}


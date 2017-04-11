\begin{code}
module motivation where

open import indexed
open import var

open import Data.Nat
open import Function

\end{code}


%<*tm>
\begin{code}
data Lam : ℕ → Set where
  V : [ Var        ⟶ Lam ]
  A : [ Lam ⟶ Lam  ⟶ Lam ]
  L : [ suc ⊢ Lam  ⟶ Lam ]
\end{code}
%</tm>
\begin{code}

module _ where

 private

   extend : ∀ {m n} → (Var m → Var n) → (Var (suc m) → Var (suc n))
   extend ρ z     = z
   extend ρ (s k) = s (ρ k)

   ⟦V⟧ : ∀ {n} → Var n → Lam n
   ⟦V⟧ = V
\end{code}
%<*ren>
\begin{code}
 ren : {m n : ℕ} → (Var m → Var n) → Lam m → Lam n
 ren ρ (V k)    = ⟦V⟧ (ρ k)
 ren ρ (A f t)  = A (ren ρ f) (ren ρ t)
 ren ρ (L b)    = L (ren (extend ρ) b)
\end{code}
%</ren>
\begin{code}
module _ where

 private

   extend : ∀ {m n} → (Var m → Lam n) → (Var (suc m) → Lam (suc n))
   extend ρ z     = V z
   extend ρ (s k) = ren s (ρ k)

   ⟦V⟧ : ∀ {n} → Lam n → Lam n
   ⟦V⟧ x = x
\end{code}
%<*sub>
\begin{code}
 sub : {m n : ℕ} → (Var m → Lam n) → Lam m → Lam n
 sub ρ (V k)    = ⟦V⟧ (ρ k)
 sub ρ (A f t)  = A (sub ρ f) (sub ρ t)
 sub ρ (L b)    = L (sub (extend ρ) b)
\end{code}
%</sub>

\begin{code}
open import environment hiding (extend ; _>>_ ; refl)
\end{code}

%<*rsem>
\begin{code}
record Sem (𝓥 𝓒 : ℕ → Set) : Set where
  field  th^𝓥 : Thinnable 𝓥
         ⟦V⟧   : [ 𝓥          ⟶ 𝓒 ]
         ⟦A⟧   : [ 𝓒 ⟶ 𝓒      ⟶ 𝓒 ]
         ⟦L⟧   : [ □ (𝓥 ⟶ 𝓒)  ⟶ 𝓒 ]
\end{code}
%</rsem>

\begin{code}
module _ {𝓥 𝓒} (𝓢 : Sem 𝓥 𝓒) where
 open Sem 𝓢
\end{code}

%<*sem>
\begin{code}
 sem : {m n : ℕ} → (m ─Env) 𝓥 n → (Lam m → 𝓒 n)
 sem ρ (V k)    = ⟦V⟧ (lookup ρ k)
 sem ρ (A f t)  = ⟦A⟧ (sem ρ f) (sem ρ t)
 sem ρ (L b)    = ⟦L⟧ (λ σ v → sem (extend σ ρ v) b)
\end{code}
%</sem>
\begin{code}
   where

     extend : ∀ {m n p} → (n ⊆ p) → (m ─Env) 𝓥 n → 𝓥 p → (suc m ─Env) 𝓥 p
     lookup (extend σ ρ v) z      = v
     lookup (extend σ ρ v) (s k)  = th^𝓥 (lookup ρ k) σ
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
Printing : Sem (λ _ → String) (λ _ → State ℕ String)
Printing = record
   { th^𝓥  = λ t _ → t
   ; ⟦V⟧    = return
   ; ⟦A⟧    =  λ mf mt → mf >>= λ f → mt >>= λ t →
               return $ f ++ "(" ++ t ++ ")"
   ; ⟦L⟧    =  λ mb → get >>= λ x → put (suc x) >>
               let x' = show x in mb (pack s) x' >>= λ b →
               return $ "λ" ++ x' ++ "." ++ b }
\end{code}
%</semprint>
\begin{code}
  where open RawMonadState (StateMonadState ℕ)
\end{code}


\begin{code}
print : Lam 0 → String
print t = proj₁ $ sem Printing {m = 0} {n = 0} (pack λ ()) t 0

_ : print (L (V z)) ≡ "λ0.0"
_ = refl

_ : print (L (L (A (V (s z)) (A (V (s z)) (V z))))) ≡ "λ0.λ1.0(0(1))"
_ = refl
\end{code}


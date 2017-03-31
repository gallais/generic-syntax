\begin{code}
module environment where

open import Data.Nat as ℕ
open import Data.Fin
open import Data.Sum
open import Function

open import indexed

infix 5 _─Env
record _─Env (m : ℕ) (𝓥 : ℕ → Set) (n : ℕ) : Set where
  constructor pack
  field lookup : Fin m → 𝓥 n
open _─Env public

ε : ∀ {𝓥 n} → (0 ─Env) 𝓥 n
lookup ε ()

_<$>_ : {𝓥 𝓦 : ℕ → Set} {m n p : ℕ} → (𝓥 n → 𝓦 p) → (m ─Env) 𝓥 n → (m ─Env) 𝓦 p
lookup (f <$> ρ) k = f (lookup ρ k)

split : ∀ m {n} → Fin (m ℕ.+ n) → Fin m ⊎ Fin n
split zero    k       = inj₂ k
split (suc m) zero    = inj₁ zero
split (suc m) (suc k) = map suc id $ split m k

_>>_ : ∀ {𝓥 m n p} → (m ─Env) 𝓥 p → (n ─Env) 𝓥 p → (m ℕ.+ n ─Env) 𝓥 p
lookup (ρ₁ >> ρ₂) k = [ lookup ρ₁ , lookup ρ₂ ]′ (split _ k)

infixl 10 _∙_
_∙_ : ∀ {𝓥 m n} → (m ─Env) 𝓥 n → 𝓥 n → (suc m ─Env) 𝓥 n
lookup (ρ ∙ v) zero    = v
lookup (ρ ∙ v) (suc k) = lookup ρ k

infix 2 _⊆_
_⊆_ : ℕ → ℕ → Set
m ⊆ n = (m ─Env) Fin n

refl : ∀ {m} → m ⊆ m
refl = pack id

select : ∀ {m n p 𝓥} → m ⊆ n → (n ─Env) 𝓥 p → (m ─Env) 𝓥 p
lookup (select ren ρ) k = lookup ρ (lookup ren k)

extend : ∀ {n} → n ⊆ suc n
extend = pack suc

□ : (ℕ → Set) → (ℕ → Set)
(□ T) m = {n : ℕ} → m ⊆ n → T n

extract : {T : ℕ → Set} → [ □ T ⟶ T ]
extract = _$ refl

join : {T : ℕ → Set} → [ □ (□ T) ⟶ □ T ]
join = extract

duplicate : {T : ℕ → Set} → [ □ T ⟶ □ (□ T) ]
duplicate t ρ σ = t (select ρ σ)

Thinnable : (ℕ → Set) → Set
Thinnable 𝓥 = [ 𝓥 ⟶ □ 𝓥 ]

th^Fin : Thinnable Fin
th^Fin v ρ = lookup ρ v

th^Env : ∀ {m 𝓥} → Thinnable 𝓥 → Thinnable ((m ─Env) 𝓥)
lookup (th^Env th^𝓥 ρ ren) k = th^𝓥 (lookup ρ k) ren

th^□ : ∀ {T} → Thinnable (□ T)
th^□ = duplicate
\end{code}

%<*kripke>
\begin{code}
Kripke : (𝓥 𝓒 : ℕ → Set) → (ℕ → ℕ → Set)
Kripke 𝓥 𝓒 0 = 𝓒
Kripke 𝓥 𝓒 m = □ ((m ─Env) 𝓥 ⟶ 𝓒)
\end{code}
%</kripke>

\begin{code}
th^Kr : {𝓥 𝓒 : ℕ → Set} (m : ℕ) → Thinnable 𝓒 → Thinnable (Kripke 𝓥 𝓒 m)
th^Kr zero     th^𝓒 = th^𝓒
th^Kr (suc _)  th^𝓒 = th^□
\end{code}

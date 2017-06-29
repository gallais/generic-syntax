\begin{code}
module environment {I : Set} where

open import Data.Nat.Base as ℕ
open import Data.List.Base hiding ([_])
open import Data.Sum as S
open import Function

open import indexed
open import var hiding (_<$>_)

infix 3 _─Env
\end{code}
%<*env>
\begin{code}
record _─Env (Γ : List I) (𝓥 : I ─Scoped) (Δ : List I) : Set where
  constructor pack; field lookup : {i : I} → Var i Γ → 𝓥 i Δ
\end{code}
%</env>
\begin{code}
open _─Env public

\end{code}
%<*thinning>
\begin{code}
Thinning : List I → List I → Set
Thinning Γ Δ = (Γ ─Env) Var Δ
\end{code}
%</thinning>
\begin{code}

ε : ∀ {𝓥 n} → ([] ─Env) 𝓥 n
lookup ε ()

_<$>_ : {𝓥 𝓦 : I ─Scoped} {Γ Δ Θ : List I} → ({i : I} → 𝓥 i Δ → 𝓦 i Θ) → (Γ ─Env) 𝓥 Δ → (Γ ─Env) 𝓦 Θ
lookup (f <$> ρ) k = f (lookup ρ k)

split : ∀ {Δ} {i : I} Γ → Var i (Γ ++ Δ) → Var i Γ ⊎ Var i Δ
split []      k     = inj₂ k
split (σ ∷ Γ) z     = inj₁ z
split (σ ∷ Γ) (s k) = S.map s id $ split Γ k

_>>_ : ∀ {𝓥 Γ Δ Θ} → (Γ ─Env) 𝓥 Θ → (Δ ─Env) 𝓥 Θ → (Γ ++ Δ ─Env) 𝓥 Θ
lookup (ρ₁ >> ρ₂) k = [ lookup ρ₁ , lookup ρ₂ ]′ (split _ k)

infixl 10 _∙_
_∙_ : ∀ {𝓥 Γ Δ σ} → (Γ ─Env) 𝓥 Δ → 𝓥 σ Δ → (σ ∷ Γ ─Env) 𝓥 Δ
lookup (ρ ∙ v) z    = v
lookup (ρ ∙ v) (s k) = lookup ρ k

refl : ∀ {Γ} → Thinning Γ Γ
refl = pack id

select : ∀ {Γ Δ Θ 𝓥} → Thinning Γ Δ → (Δ ─Env) 𝓥 Θ → (Γ ─Env) 𝓥 Θ
lookup (select ren ρ) k = lookup ρ (lookup ren k)

extend : ∀ {Γ σ} → Thinning Γ (σ ∷ Γ)
extend = pack s

\end{code}
%<*box>
\begin{code}
□ : (List I → Set) → (List I → Set)
(□ T) Γ = [ Thinning Γ ⟶ T ]
\end{code}
%</box>
%<*comonad>
\begin{code}
extract    : {T : List I → Set} → [ □ T ⟶ T        ]
duplicate  : {T : List I → Set} → [ □ T ⟶ □ (□ T)  ]
\end{code}
%</comonad>
\begin{code}
extract t = t refl
duplicate t ρ σ = t (select ρ σ)

join : {T : List I → Set} → [ □ (□ T) ⟶ □ T ]
join = extract

\end{code}
%<*thinnable>
\begin{code}
Thinnable : (List I → Set) → Set
Thinnable T = [ T ⟶ □ T ]
\end{code}
%</thinnable>
\begin{code}

th^Var : {i : I} → Thinnable (Var i)
th^Var v ρ = lookup ρ v

th^Env : ∀ {Γ 𝓥} → ({i : I} → Thinnable (𝓥 i)) → Thinnable ((Γ ─Env) 𝓥)
lookup (th^Env th^𝓥 ρ ren) k = th^𝓥 (lookup ρ k) ren
\end{code}
%<*freeth>
\begin{code}
th^□ : {T : List I → Set} → Thinnable (□ T)
th^□ = duplicate
\end{code}
%</freeth>
%<*kripke>
\begin{code}
Kripke : (𝓥 𝓒 : I ─Scoped) → (List I → I ─Scoped)
Kripke 𝓥 𝓒 [] i = 𝓒 i
Kripke 𝓥 𝓒 Γ  i = □ ((Γ ─Env) 𝓥 ⟶ 𝓒 i)
\end{code}
%</kripke>

\begin{code}
th^Kr : {𝓥 𝓒 : I ─Scoped}
        (Γ : List I) → ({i : I} → Thinnable (𝓒 i)) → {i : I} → Thinnable (Kripke 𝓥 𝓒 Γ i)
th^Kr []       th^𝓒 = th^𝓒
th^Kr (_ ∷ _)  th^𝓒 = th^□
\end{code}

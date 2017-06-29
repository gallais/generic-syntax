\begin{code}
module Generic.Semantics where

open import Size
open import Data.Bool
open import Data.List.Base as L hiding ([_])
open import Data.Product as P hiding (,_)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import var
open import indexed
open import environment as E hiding (refl)
open import Generic.Syntax

\end{code}
%<*semantics>
\begin{code}
Alg : {I : Set} (d : Desc I) (𝓥 𝓒 : I ─Scoped) → Set
Alg {I} d 𝓥 𝓒 = {i : I} → [ ⟦ d ⟧ (Kripke 𝓥 𝓒) i ⟶ 𝓒 i ]

record Sem {I : Set} (d : Desc I) (𝓥 𝓒 : I ─Scoped) : Set where
  field  th^𝓥   : {i : I} → Thinnable (𝓥 i)
         var    : {i : I} → [ 𝓥 i                  ⟶ 𝓒 i ]
         alg    : Alg d 𝓥 𝓒
\end{code}
%</semantics>

%<*sembody>
\begin{code}
  _─Comp : (Γ : List I) (𝓒 : I ─Scoped) (Δ : List I) → Set
  (Γ ─Comp) 𝓒 Δ = {s : Size} {i : I} → Tm d s i Γ → 𝓒 i Δ

  sem   :  {Γ Δ : List I} → (Γ ─Env) 𝓥 Δ → (Γ ─Comp) 𝓒 Δ
  body  :  {Γ Δ : List I} {s : Size} → (Γ ─Env) 𝓥 Δ →
           ∀ Θ i → Scope (Tm d s) Θ i Γ → Kripke 𝓥 𝓒 Θ i Δ
\end{code}
%</sembody>
%<*sem>
\begin{code}
  sem ρ (`var k) = var (lookup ρ k)
  sem ρ (`con t) = alg (fmap d (body ρ) t)
\end{code}
%</sem>
%<*body>
\begin{code}
  body ρ []       i t = sem ρ t
  body ρ (_ ∷ _)  i t = λ ren vs → sem (vs >> th^Env th^𝓥 ρ ren) t
\end{code}
%</body>
%<*closed>
\begin{code}
  closed : ([] ─Comp) 𝓒 []
  closed = sem ε
\end{code}
%</closed>
\begin{code}
open import varlike
module _ {I : Set} where
\end{code}
%<*reify>
\begin{code}
 reify : {𝓥 𝓒 : I ─Scoped} → VarLike 𝓥 →
         {Γ : List I} → ∀ Δ i → Kripke 𝓥 𝓒 Δ i Γ → Scope 𝓒 Δ i Γ
 reify vl^𝓥 []        i b = b
 reify vl^𝓥 Δ@(_ ∷ _) i b = b (freshʳ vl^Var Δ) (freshˡ vl^𝓥 _)
\end{code}

%</reify>
\begin{code}
 record Syntactic (d : Desc I) (𝓥 : I ─Scoped) : Set where
   field
     var    : {i : I} → [ 𝓥 i ⟶ Tm d ∞ i ]
     vl^𝓥  : VarLike 𝓥

   semantics : Sem d 𝓥 (Tm d ∞)
   Sem.var   semantics = var
   Sem.th^𝓥  semantics = th^𝓥 vl^𝓥
   Sem.alg   semantics = `con ∘ fmap d (reify vl^𝓥)

sy^Var : {I : Set} {d : Desc I} → Syntactic d Var
Syntactic.var    sy^Var = `var
Syntactic.vl^𝓥  sy^Var = vl^Var
\end{code}
%<*renaming>
\begin{code}
Renaming : {I : Set} (d : Desc I) → Sem d Var (Tm d ∞)
Sem.th^𝓥  (Renaming d) = λ k ρ → lookup ρ k
Sem.var   (Renaming d) = `var
Sem.alg   (Renaming d) = `con ∘ fmap d (reify vl^Var)

ren :  {I : Set} {Γ Δ : List I} {i : I} → ∀ d → (Γ ─Env) Var Δ →
       Tm d ∞ i Γ → Tm d ∞ i Δ
ren d ρ t = Sem.sem (Renaming d) ρ t
\end{code}
%</renaming>
\begin{code}
th^Tm : {I : Set} {d : Desc I} {i : I} → Thinnable (Tm d ∞ i)
th^Tm t ρ = Sem.sem (Renaming _) ρ t

vl^Tm : {I : Set} {d : Desc I} → VarLike (Tm d ∞)
new   vl^Tm = `var z
th^𝓥  vl^Tm = th^Tm

sy^Tm : {I : Set} {d : Desc I} → Syntactic d (Tm d ∞)
Syntactic.var   sy^Tm = id
Syntactic.vl^𝓥  sy^Tm = vl^Tm

\end{code}
%<*substitution>
\begin{code}
Substitution : {I : Set} (d : Desc I) → Sem d (Tm d ∞) (Tm d ∞)
Sem.th^𝓥  (Substitution d) = λ t ρ → Sem.sem (Renaming d) ρ t
Sem.var   (Substitution d) = id
Sem.alg   (Substitution d) = `con ∘ fmap d (reify vl^Tm)

sub : {I : Set} {Γ Δ : List I} {i : I} → ∀ d → (Γ ─Env) (Tm d ∞) Δ →
      Tm d ∞ i Γ → Tm d ∞ i Δ
sub d ρ t = Sem.sem (Substitution d) ρ t
\end{code}
%</substitution>

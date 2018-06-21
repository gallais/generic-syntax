\begin{code}
module Generic.Semantics where

open import Size
open import Data.Bool
open import Data.List.Base as L hiding ([_])
open import Data.Product as P hiding (,_)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import var
open import rel
open import indexed
open import environment as E
open import Generic.Syntax

module _ {I : Set} where

 Alg : (d : Desc I) (𝓥 𝓒 : I ─Scoped) → Set
 Alg d 𝓥 𝓒 = {i : I} → [ ⟦ d ⟧ (Kripke 𝓥 𝓒) i ⟶ 𝓒 i ]

module _ {I : Set} {d : Desc I} where
\end{code}
%<*comp>
\begin{code}
 _─Comp : List I → I ─Scoped → List I → Set
 (Γ ─Comp) 𝓒 Δ = {s : Size} {i : I} → Tm d s i Γ → 𝓒 i Δ
\end{code}
%</comp>
%<*semantics>
\begin{code}
record Sem {I : Set} (d : Desc I) (𝓥 𝓒 : I ─Scoped) : Set where
 field  th^𝓥   : {i : I} → Thinnable (𝓥 i)
        var    : {i : I} → [ 𝓥 i                   ⟶ 𝓒 i ]
        alg    : {i : I} → [ ⟦ d ⟧ (Kripke 𝓥 𝓒) i  ⟶ 𝓒 i ]
\end{code}
%</semantics>
%<*semtype>
\begin{code}
 sem   :  {Γ Δ : List I} → (Γ ─Env) 𝓥 Δ → (Γ ─Comp) 𝓒 Δ
 body  :  {Γ Δ : List I} {s : Size} → (Γ ─Env) 𝓥 Δ → ∀ Θ i → Scope (Tm d s) Θ i Γ → Kripke 𝓥 𝓒 Θ i Δ
\end{code}
%</semtype>
%<*sem>
\begin{code}
 sem ρ (`var k) = var (lookup ρ k)
 sem ρ (`con t) = alg (fmap d (body ρ) t)
\end{code}
%</sem>
%<*body>
\begin{code}
 body ρ []       i t = sem ρ t
 body ρ (_ ∷ _)  i t = λ σ vs → sem (vs >> th^Env th^𝓥 ρ σ) t
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
module _ {I : Set} {𝓥 𝓒 : I ─Scoped} where
\end{code}
%<*reify>
\begin{code}
 reify : VarLike 𝓥 → {Γ : List I} → ∀ Δ i → Kripke 𝓥 𝓒 Δ i Γ → Scope 𝓒 Δ i Γ
 reify vl^𝓥 []         i b = b
 reify vl^𝓥 Δ@(_ ∷ _)  i b = b (freshʳ vl^Var Δ) (freshˡ vl^𝓥 _)
\end{code}

%</reify>
\begin{code}
module _ {I : Set} where

 record Syntactic (d : Desc I) (𝓥 : I ─Scoped) : Set where
   field
     var    : {i : I} → [ 𝓥 i ⟶ Tm d ∞ i ]
     vl^𝓥  : VarLike 𝓥

   semantics : Sem d 𝓥 (Tm d ∞)
   Sem.var   semantics = var
   Sem.th^𝓥  semantics = th^𝓥 vl^𝓥
   Sem.alg   semantics = `con ∘ fmap d (reify vl^𝓥)

module _ {I : Set} {d : Desc I} where

 sy^Var : Syntactic d Var
 Syntactic.var    sy^Var = `var
 Syntactic.vl^𝓥  sy^Var = vl^Var

-- Records are better for the paper, definitions using
-- copatterns are better for the legibility of goals...
module OnlyForDisplayRenaming {I : Set} {d : Desc I} where
\end{code}
%<*renaming>
\begin{code}
 Renaming : Sem d Var (Tm d ∞)
 Renaming = record
   { th^𝓥  = λ k ρ → lookup ρ k
   ; var   = `var
   ; alg   = `con ∘ fmap d (reify vl^Var) }

 ren :  {Γ Δ : List I} → (Γ ─Env) Var Δ →
        (Γ ─Comp) (Tm d ∞) Δ
 ren = Sem.sem Renaming
\end{code}
%</renaming>
\begin{code}
module _ {I : Set} {d : Desc I} where

 Renaming : Sem d Var (Tm d ∞)
 Sem.th^𝓥  Renaming = λ k ρ → lookup ρ k
 Sem.var   Renaming = `var
 Sem.alg   Renaming = `con ∘ fmap d (reify vl^Var)

 ren :  {Γ Δ : List I} → (Γ ─Env) Var Δ →
        (Γ ─Comp) (Tm d ∞) Δ
 ren = Sem.sem Renaming

 th^Tm : {i : I} → Thinnable (Tm d ∞ i)
 th^Tm t ρ = Sem.sem Renaming ρ t

 vl^Tm : VarLike (Tm d ∞)
 new   vl^Tm = `var z
 th^𝓥  vl^Tm = th^Tm

 reify^Tm : ∀ Δ {σ} → [ Kripke (Tm d ∞) (Tm d ∞) Δ σ ⟶ (Δ ++_) ⊢ Tm d ∞ σ ]
 reify^Tm Δ = reify vl^Tm Δ _

 lookup-base^Tm : {Γ : List I} {σ : I} (k : Var σ Γ) → lookup (base vl^Tm) k ≡ `var k
 lookup-base^Tm z                              = refl
 lookup-base^Tm (s k) rewrite lookup-base^Tm k = refl

 base^VarTm^R : ∀ {Γ} → ∀[ VarTm^R ] (base vl^Var {Γ}) (base vl^Tm)
 lookup^R base^VarTm^R k = begin
   `var (lookup (base vl^Var) k) ≡⟨ cong `var (lookup-base^Var k) ⟩
   `var k                        ≡⟨ sym (lookup-base^Tm k) ⟩
   lookup (base vl^Tm) k ∎

 sy^Tm : Syntactic d (Tm d ∞)
 Syntactic.var   sy^Tm = id
 Syntactic.vl^𝓥  sy^Tm = vl^Tm

-- Same thing as with Renaming
module OnlyForDisplaySubstitution {I : Set} {d : Desc I} where
\end{code}
%<*substitution>
\begin{code}
 Substitution : Sem d (Tm d ∞) (Tm d ∞)
 Substitution = record
   { th^𝓥  = λ t ρ → ren ρ t
   ; var   = id
   ; alg   = `con ∘ fmap d (reify vl^Tm) }

 sub :  {Γ Δ : List I} → (Γ ─Env) (Tm d ∞) Δ →
        (Γ ─Comp) (Tm d ∞) Δ
 sub = Sem.sem Substitution
\end{code}
%</substitution>
\begin{code}
module _ {I : Set} {d : Desc I} where

 Substitution : Sem d (Tm d ∞) (Tm d ∞)
 Sem.th^𝓥  Substitution = λ t ρ → ren ρ t
 Sem.var   Substitution = id
 Sem.alg   Substitution = `con ∘ fmap d (reify vl^Tm)

 sub :  {Γ Δ : List I} → (Γ ─Env) (Tm d ∞) Δ →
        (Γ ─Comp) (Tm d ∞) Δ
 sub = Sem.sem Substitution

 infix 5 _[_
 infix 6 _/0]

 _/0] : ∀ {σ Γ} → Tm d ∞ σ Γ → (σ ∷ Γ ─Env) (Tm d ∞) Γ
 _/0] = singleton vl^Tm

 _[_ : ∀ {σ τ Γ} → Tm d ∞ τ (σ ∷ Γ) → (σ ∷ Γ ─Env) (Tm d ∞) Γ → Tm d ∞ τ Γ
 t [ ρ = sub ρ t
\end{code}

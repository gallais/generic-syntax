\begin{code}
{-# OPTIONS --sized-types #-}
module Generic.Semantics.NbyE where

open import Size
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.List.Base hiding ([_])
open import Function
open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Var using (Var; _─Scoped)
open import Data.Var.Varlike
open import Data.Environment hiding (_<$>_; sequenceA)
open import Generic.Syntax
open import Generic.Semantics

private
  variable
    I : Set
    s : Size
    σ : I
    d : Desc I

\end{code}
%<*domain>
\begin{code}
{-# NO_POSITIVITY_CHECK #-}
data Dm (d : Desc I) : Size → I ─Scoped where
  V : ∀[ Var σ ⇒ Dm d s σ ]
  C : ∀[ ⟦ d ⟧ (Kripke (Dm d s) (Dm d s)) σ ⇒ Dm d (↑ s)  σ ]
  ⊥ : ∀[ Dm d (↑ s) σ ]
\end{code}
%</domain>
\begin{code}
module _ {d : Desc I} where

  th^Dm : Thinnable (Dm d s σ)
  th^Dm (V k) ρ = V (th^Var k ρ)
  th^Dm (C t) ρ = C (fmap d (λ Θ i kr → th^Kr Θ th^Dm kr ρ) t)
  th^Dm ⊥     ρ = ⊥

vl^Dm : VarLike (Dm d s)
vl^Dm = record { new = V Var.z ; th^𝓥 = th^Dm }


open import Data.Maybe.Base
import Data.Maybe.Categorical as Maybe
import Category.Monad as CM
open import Level
private module M = CM.RawMonad (Maybe.monad {zero})
instance _ = M.rawIApplicative
open M

Alg : (d : Desc I) (𝓥 𝓒 : I ─Scoped) → Set
Alg d 𝓥 𝓒 = ∀ {σ Γ} → ⟦ d ⟧ (Kripke 𝓥 𝓒) σ Γ → 𝓒 σ Γ

module _ {I : Set} {d : Desc I} where
\end{code}
%<*nbe-setup>
\begin{code}
 reify^Dm  : ∀[ Dm d s σ ⇒ Maybe ∘ Tm d ∞ σ ]
 nbe       : Alg d (Dm d ∞) (Dm d ∞) → Semantics d (Dm d ∞) (Dm d ∞)

 norm      : Alg d (Dm d ∞) (Dm d ∞) → ∀[ Tm d ∞ σ ⇒ Maybe ∘ Tm d ∞ σ ]
 norm alg  = reify^Dm ∘ Semantics.semantics (nbe alg) (base vl^Dm)
\end{code}
%</nbe-setup>
\begin{code}
 reify^Dm (V k) = just (`var k)
 reify^Dm (C v) = `con <$> mapA d (λ Θ i → reify^Dm ∘ reify vl^Dm Θ i) v
 reify^Dm ⊥     = nothing

 Semantics.th^𝓥  (nbe alg) = th^Dm
 Semantics.var   (nbe alg) = id
 Semantics.alg   (nbe alg) = alg
\end{code}

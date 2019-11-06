\begin{code}
{-# OPTIONS --safe --sized-types #-}

open import Data.Var hiding (_<$>_; z; s)
open import Data.Relation

module Generic.Simulation {I : Set} {𝓥ᴬ 𝓥ᴮ 𝓒ᴬ 𝓒ᴮ : I ─Scoped} where

open import Size
open import Data.List hiding ([_] ; lookup ; zip)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Relation.Unary

open import Data.Var.Varlike
open import Data.Environment
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Relator as Relator using (⟦_⟧ᴿ; liftᴿ)

private
  variable
    Γ Δ : List I
    σ : I
    vᴬ : 𝓥ᴬ σ Γ
    vᴮ : 𝓥ᴮ σ Γ
    s : Size
    ρᴬ : (Γ ─Env) 𝓥ᴬ Δ
    ρᴮ : (Γ ─Env) 𝓥ᴮ Δ

module _ (𝓥ᴿ  : Rel 𝓥ᴬ 𝓥ᴮ) (𝓒ᴿ  : Rel 𝓒ᴬ 𝓒ᴮ) where

  reifyᴿ : {vlᴬ : VarLike 𝓥ᴬ} {vlᴮ : VarLike 𝓥ᴮ} (vlᴿ : VarLikeᴿ 𝓥ᴿ vlᴬ vlᴮ) →
           ∀ Δ σ → {kᴬ : Kripke 𝓥ᴬ 𝓒ᴬ Δ σ Γ} {kᴮ : Kripke 𝓥ᴮ 𝓒ᴮ Δ σ Γ} →
           Kripkeᴿ 𝓥ᴿ 𝓒ᴿ Δ σ kᴬ kᴮ → rel 𝓒ᴿ σ (reify vlᴬ Δ σ kᴬ) (reify vlᴮ Δ σ kᴮ)
  reifyᴿ vlᴿ []         σ kᴿ = kᴿ
  reifyᴿ vlᴿ Δ@(_ ∷ _)  σ kᴿ = kᴿ (freshʳ vl^Var Δ) (VarLikeᴿ.freshˡᴿ vlᴿ _)

  private
   module DISPLAYONLY where
\end{code}
%<*recsim1>
\begin{code}
   record Simulation (d : Desc I)
     (𝓢ᴬ : Semantics d 𝓥ᴬ 𝓒ᴬ) (𝓢ᴮ : Semantics d 𝓥ᴮ 𝓒ᴮ)
     (𝓥ᴿ  : Rel 𝓥ᴬ 𝓥ᴮ) (𝓒ᴿ  : Rel 𝓒ᴬ 𝓒ᴮ) : Set where
     module 𝓢ᴬ = Semantics 𝓢ᴬ
     module 𝓢ᴮ = Semantics 𝓢ᴮ
     field  thᴿ   :  (ρ : Thinning Γ Δ) → rel 𝓥ᴿ σ vᴬ vᴮ →
                     rel 𝓥ᴿ σ (𝓢ᴬ.th^𝓥 vᴬ ρ) (𝓢ᴮ.th^𝓥 vᴮ ρ)
            varᴿ  : rel 𝓥ᴿ σ vᴬ vᴮ → rel 𝓒ᴿ σ (𝓢ᴬ.var vᴬ) (𝓢ᴮ.var vᴮ)
     bodyᴿ : ⟦ d ⟧ (Kripke 𝓥ᴬ 𝓒ᴬ) σ Δ → ⟦ d ⟧ (Kripke 𝓥ᴮ 𝓒ᴮ) σ Δ → Set
     bodyᴿ vᴬ vᴮ = ⟦ d ⟧ᴿ (Kripkeᴿ 𝓥ᴿ 𝓒ᴿ) vᴬ vᴮ
     field  algᴿ  : (b : ⟦ d ⟧ (Scope (Tm d s)) σ Γ) → All 𝓥ᴿ Γ ρᴬ ρᴮ →
                    let  vᴬ = fmap d (𝓢ᴬ.body ρᴬ) b
                         vᴮ = fmap d (𝓢ᴮ.body ρᴮ) b
                    in bodyᴿ vᴬ vᴮ → rel 𝓒ᴿ σ (𝓢ᴬ.alg vᴬ) (𝓢ᴮ.alg vᴮ)
\end{code}
%</recsim1>

%<*recsim>
\begin{code}
record Simulation (d : Desc I)
  (𝓢ᴬ : Semantics d 𝓥ᴬ 𝓒ᴬ) (𝓢ᴮ : Semantics d 𝓥ᴮ 𝓒ᴮ)
  (𝓥ᴿ  : Rel 𝓥ᴬ 𝓥ᴮ) (𝓒ᴿ  : Rel 𝓒ᴬ 𝓒ᴮ) : Set where
\end{code}
%</recsim>
\begin{code}
  module 𝓢ᴬ = Semantics 𝓢ᴬ
  module 𝓢ᴮ = Semantics 𝓢ᴮ
  field
\end{code}
%<*thR>
\begin{code}
    thᴿ   :  (ρ : Thinning Γ Δ) → rel 𝓥ᴿ σ vᴬ vᴮ → rel 𝓥ᴿ σ (𝓢ᴬ.th^𝓥 vᴬ ρ) (𝓢ᴮ.th^𝓥 vᴮ ρ)
\end{code}
%</thR>
%<*varR>
\begin{code}
    varᴿ  : rel 𝓥ᴿ σ vᴬ vᴮ → rel 𝓒ᴿ σ (𝓢ᴬ.var vᴬ) (𝓢ᴮ.var vᴮ)
\end{code}
%</varR>
%<*bodyR>
\begin{code}
  bodyᴿ : ⟦ d ⟧ (Kripke 𝓥ᴬ 𝓒ᴬ) σ Δ → ⟦ d ⟧ (Kripke 𝓥ᴮ 𝓒ᴮ) σ Δ → Set
  bodyᴿ vᴬ vᴮ = ⟦ d ⟧ᴿ (Kripkeᴿ 𝓥ᴿ 𝓒ᴿ) vᴬ vᴮ
\end{code}
%</bodyR>
\begin{code}
  field
\end{code}
%<*algR>
\begin{code}
    algᴿ  : (b : ⟦ d ⟧ (Scope (Tm d s)) σ Γ) → All 𝓥ᴿ Γ ρᴬ ρᴮ →
            let  vᴬ = fmap d (𝓢ᴬ.body ρᴬ) b
                 vᴮ = fmap d (𝓢ᴮ.body ρᴮ) b
            in bodyᴿ vᴬ vᴮ → rel 𝓒ᴿ σ (𝓢ᴬ.alg vᴬ) (𝓢ᴮ.alg vᴮ)
\end{code}
%</algR>
%<*simbody>
\begin{code}
  sim   :  All 𝓥ᴿ Γ ρᴬ ρᴮ → (t : Tm d s σ Γ) →
           rel 𝓒ᴿ σ (𝓢ᴬ.semantics ρᴬ t) (𝓢ᴮ.semantics ρᴮ t)
  body  :  All 𝓥ᴿ Γ ρᴬ ρᴮ → ∀ Δ j → (t : Scope (Tm d s) Δ j Γ) →
           Kripkeᴿ 𝓥ᴿ 𝓒ᴿ Δ j (𝓢ᴬ.body ρᴬ Δ j t) (𝓢ᴮ.body ρᴮ Δ j t)

  sim ρᴿ (`var k) = varᴿ (lookupᴿ ρᴿ k)
  sim ρᴿ (`con t) = algᴿ t ρᴿ (liftᴿ d (body ρᴿ) t)

  body ρᴿ []       i t = sim ρᴿ t
  body ρᴿ (_ ∷ _)  i t = λ σ vsᴿ → sim (vsᴿ >>ᴿ (thᴿ σ <$>ᴿ ρᴿ)) t
\end{code}
%</simbody>

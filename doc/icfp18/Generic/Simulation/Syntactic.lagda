\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Simulation.Syntactic where

open import Size
open import Data.List hiding (lookup)
open import Function
open import Relation.Binary.PropositionalEquality

open import Data.Var.Varlike
open import Data.Environment
open import Data.Relation as Relation
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Relator as Relator
open import Generic.Simulation as Simulation
open Simulation.Simulation

module _ {I : Set} {d : Desc I} where

\end{code}
%<*renext>
\begin{code}
 RenExt : Simulation d Ren Ren Eqᴿ Eqᴿ
 RenExt .thᴿ   = λ ρ → cong (lookup ρ)
 RenExt .varᴿ  = cong `var
 RenExt .algᴿ  = λ _ _ →
   cong `con ∘ Relator.reifyᴿ Eqᴿ d (Simulation.reifyᴿ Eqᴿ Eqᴿ (vl^Refl vl^Var))
\end{code}
%</renext>
%<*subext>
\begin{code}
 SubExt : Simulation d Sub Sub Eqᴿ Eqᴿ
 SubExt .thᴿ   = λ ρ → cong (ren ρ)
 SubExt .varᴿ  = id
 SubExt .algᴿ  = λ _ _ →
   cong `con ∘ Relator.reifyᴿ Eqᴿ d (Simulation.reifyᴿ Eqᴿ Eqᴿ (vl^Refl vl^Tm))
\end{code}
%</subext>
%<*rensub>
\begin{code}
 RenSub : Simulation d Ren Sub VarTmᴿ Eqᴿ
\end{code}
%</rensub>
\begin{code}
 RenSub .varᴿ  = id
 RenSub .thᴿ   = λ ρ → cong (λ t → th^Tm t ρ)
 RenSub .algᴿ  = λ _ _ →
   cong `con ∘ Relator.reifyᴿ VarTmᴿ d (Simulation.reifyᴿ VarTmᴿ Eqᴿ vl^VarTm)

 private
   variable
     Γ Δ : List I
     σ : I

\end{code}
%<*rensubfun>
\begin{code}
 rensub : (ρ : Thinning Γ Δ) (t : Tm d ∞ σ Γ) → ren ρ t ≡ sub (`var <$> ρ) t
 rensub ρ = Simulation.sim RenSub (packᴿ λ _ → refl)
\end{code}
%</rensubfun>

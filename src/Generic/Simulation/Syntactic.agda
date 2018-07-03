module Generic.Simulation.Syntactic where

open import Size
open import Data.List hiding (lookup)
open import Function
open import Relation.Binary.PropositionalEquality

open import varlike
open import environment
open import rel
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Zip
open import Generic.Simulation

module _ {I : Set} {d : Desc I} where

 RenExt : Sim Eq^R Eq^R d Renaming Renaming
 Sim.th^R   RenExt = λ ρ → cong (lookup ρ)
 Sim.var^R  RenExt = cong `var
 Sim.alg^R  RenExt = λ _ _ →
   cong `con ∘ zip^reify Eq^R (reify^R Eq^R Eq^R (vl^Refl vl^Var)) d

 SubExt : Sim Eq^R Eq^R d Substitution Substitution
 Sim.th^R   SubExt = λ ρ → cong (ren ρ)
 Sim.var^R  SubExt = id
 Sim.alg^R  SubExt = λ _ _ →
   cong `con ∘ zip^reify Eq^R (reify^R Eq^R Eq^R (vl^Refl vl^Tm)) d

module _ {I : Set} {d : Desc I} where

 RenSub : Sim VarTm^R Eq^R d Renaming Substitution
 Sim.var^R  RenSub = id
 Sim.th^R   RenSub = λ { _ refl → refl }
 Sim.alg^R  RenSub = λ _ _ →
   cong `con ∘ zip^reify (mkRel (_≡_ ∘ `var)) (reify^R VarTm^R Eq^R vl^VarTm) d

 rensub : {Γ Δ : List I} (ρ : Thinning Γ Δ) {i : I} (t : Tm d ∞ i Γ) → ren ρ t ≡ sub (`var <$> ρ) t
 rensub ρ = Sim.sim RenSub (pack^R (λ _ → refl))

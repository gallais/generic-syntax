module Generic.Context where

open import Size
open import Data.List.Base as L using (List; []; _∷_)
open import Function

open import Data.Var hiding (z; s; _<$>_)
open import Relation.Unary
open import Data.Environment as E hiding (sequenceA)

open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic

private
  variable
    I : Set
    σ τ : I
    s : Size
    Δ : List I

data Cxt (d : Desc I) (σ : I) (Γ : List I) : Size → I ─Scoped where
  «─_» : ∀[ (Γ ─Env) (Tm d ∞)             ⇒ Cxt d σ Γ (↑ s) σ ]
  `trm : ∀[ Tm d ∞ τ                      ⇒ Cxt d σ Γ (↑ s) τ ]
  `con : ∀[ ⟦ d ⟧ (Scope (Cxt d σ Γ s)) τ ⇒ Cxt d σ Γ (↑ s) τ ]

module _ {d : Desc I} {σ Γ} where

  _«_» : Cxt d σ Γ s τ Δ → Tm d ∞ σ Γ → Tm d ∞ τ Δ
  «─ ρ » « t » = sub ρ t
  `trm t « _ » = t
  `con b « t » = `con (fmap d (λ _ _ → _« t ») b)


{-# OPTIONS --safe --sized-types #-}

module Motivation.Problem.Naive where

open import Relation.Unary
open import Data.Var hiding (_<$>_)
open import Data.Environment
open import Data.Relation

open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Data.List hiding ([_] ; lookup)

open import StateOfTheArt.ACMM using (Type; α; _`→_) public

private
  variable
    σ τ : Type
    Γ Δ : List Type


data S : Type ─Scoped where
  `var  : ∀[ Var σ ⇒ S σ ]
  `lam  : ∀[ (σ ∷_) ⊢ S τ ⇒ S (σ `→ τ) ]
  `app  : ∀[ S (σ `→ τ) ⇒ S σ ⇒ S τ ]
  `let  : ∀[ S σ ⇒ (σ ∷_) ⊢ S τ  ⇒ S τ ]

data T : Type ─Scoped where
  `var  : ∀[ Var σ ⇒ T σ ]
  `lam  : ∀[ (σ ∷_) ⊢ T τ ⇒ T (σ `→ τ) ]
  `app  : ∀[ T (σ `→ τ) ⇒ T σ ⇒ T τ ]

th^T : Thinnable (T σ)
th^T (`var v)    ρ = `var (lookup ρ v)
th^T (`lam b)    ρ = `lam (th^T b (th^Env th^Var ρ extend ∙ z))
th^T (`app f t)  ρ = `app (th^T f ρ) (th^T t ρ)

unlet : (Γ ─Env) T Δ → S σ Γ → T σ Δ
unlet ρ (`var v)    = lookup ρ v
unlet ρ (`lam b)    = `lam (unlet (th^Env th^T ρ extend ∙ `var z) b)
unlet ρ (`app f t)  = `app (unlet ρ f) (unlet ρ t)
unlet ρ (`let e t)  = unlet (ρ ∙ unlet ρ e) t

th^S : Thinnable (S σ)
th^S (`var v)    ρ = `var (lookup ρ v)
th^S (`lam b)    ρ = `lam (th^S b (th^Env th^Var ρ extend ∙ z))
th^S (`app f t)  ρ = `app (th^S f ρ) (th^S t ρ)
th^S (`let e t)  ρ = `let (th^S e ρ) (th^S t (th^Env th^Var ρ extend ∙ z))

sub^S : (Γ ─Env) S Δ → S σ Γ → S σ Δ
sub^S ρ (`var v)    = lookup ρ v
sub^S ρ (`lam b)    = `lam (sub^S (th^Env th^S ρ extend ∙ `var z) b)
sub^S ρ (`app f t)  = `app (sub^S ρ f) (sub^S ρ t)
sub^S ρ (`let e t)  = `let (sub^S ρ e) (sub^S (th^Env th^S ρ extend ∙ `var z) t)

sub^T : (Γ ─Env) T Δ → T σ Γ → T σ Δ
sub^T ρ (`var v)    = lookup ρ v
sub^T ρ (`lam b)    = `lam (sub^T (th^Env th^T ρ extend ∙ `var z) b)
sub^T ρ (`app f t)  = `app (sub^T ρ f) (sub^T ρ t)

_⟨_/0⟩^S : ∀[ (σ ∷_) ⊢ S τ ⇒ S σ ⇒ S τ ]
b ⟨ t /0⟩^S = sub^S (`var <$> identity ∙ t) b

_⟨_/0⟩^T : ∀[ (σ ∷_) ⊢ T τ ⇒ T σ ⇒ T τ ]
b ⟨ t /0⟩^T = sub^T (`var <$> identity ∙ t) b


module _ where
 infix 1 _⊢_∋_↝S_

 private
  variable
    b c : S τ (σ ∷ Γ)
    f g : S (σ `→ τ) Γ
    d e t u : S σ Γ

 data _⊢_∋_↝S_ : ∀ Γ σ → S σ Γ → S σ Γ → Set where
 -- computation
   β      : ∀ (b : S τ (σ ∷ Γ)) u → Γ ⊢ τ ∋ `app (`lam b) u ↝S b ⟨ u /0⟩^S
   ζ      : ∀ e (t : S τ (σ ∷ Γ)) → Γ ⊢ τ ∋ `let e t ↝S t ⟨ e /0⟩^S
 -- structural
   `lam   : (σ ∷ Γ) ⊢ τ ∋ b ↝S c → Γ ⊢ σ `→ τ ∋ `lam b ↝S `lam c
   `appl  : Γ ⊢ σ `→ τ ∋ f ↝S g → ∀ t → Γ ⊢ τ ∋ `app f t ↝S `app g t
   `appr  : ∀ f → Γ ⊢ σ ∋ t ↝S u → Γ ⊢ τ ∋ `app f t ↝S `app f u
   `letl  : Γ ⊢ σ ∋ d ↝S e → ∀ t → Γ ⊢ τ ∋ `let d t ↝S `let e t
   `letr  : ∀ e → (σ ∷ Γ) ⊢ τ ∋ t ↝S u → Γ ⊢ τ ∋ `let e t ↝S `let e u

module _ where
 infix 1 _⊢_∋_↝T_

 private
  variable
    b c : T τ (σ ∷ Γ)
    f g : T (σ `→ τ) Γ
    d e t u : T σ Γ

 data _⊢_∋_↝T_ : ∀ Γ σ → T σ Γ → T σ Γ → Set where
 -- computation
   β      : ∀ {Γ σ τ} (b : T τ (σ ∷ Γ)) u → Γ ⊢ τ ∋ `app (`lam b) u ↝T b ⟨ u /0⟩^T
 -- structural
   `lam   : (σ ∷ Γ) ⊢ τ ∋ b ↝T c → Γ ⊢ σ `→ τ ∋ `lam b ↝T `lam c
   `appl  : Γ ⊢ σ `→ τ ∋ f ↝T g → ∀ t → Γ ⊢ τ ∋ `app f t ↝T `app g t
   `appr  : ∀ f → Γ ⊢ σ ∋ t ↝T u → Γ ⊢ τ ∋ `app f t ↝T `app f u

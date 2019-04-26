\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Examples.SystemF where

open import Size
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.List.Base hiding ([_])
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Var hiding (_<$>_)
open import Data.Var.Varlike
open import Data.Environment hiding (_<$>_)
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic

data Kind : Set where
  Term Type : Kind

system-F  : Desc Kind
system-F  =   `X [] Type (`X [] Type (`∎ Type)) -- arrow
          `+  `X (Type ∷ []) Type (`∎ Type)     -- forall
          `+  `X [] Term (`X [] Term (`∎ Term)) -- app
          `+  `X (Term ∷ []) Term (`∎ Term)     -- lam
          `+  `X [] Term (`X [] Type (`∎ Term)) -- App
          `+  `X (Type ∷ []) Term (`∎ Term)     -- Lam

pattern arr a b = `con (true , a , b , refl)
pattern for b   = `con (false , true , b , refl)

pattern app f t = `con (false , false , true , f , t , refl)
pattern lam b   = `con (false , false , false , true , b , refl)

pattern App f t = `con (false , false , false , false , true , f , t , refl)
pattern Lam b   = `con (false , false , false , false , false , b , refl)

SF : Kind → List Kind → Set
SF = Tm system-F ∞

data Redex {Γ : List Kind} : SF Term Γ → Set where
  applam   : (b : SF Term (Term ∷ Γ)) (u : SF Term Γ) → Redex (app (lam b) u)
  AppLam   : (b : SF Term (Type ∷ Γ)) (u : SF Type Γ) → Redex (App (Lam b) u)
  -- congruence rules
  [app-l]  : {f : SF Term Γ} → Redex f → (t : SF Term Γ) → Redex (app f t)
  [app-r]  : (f : SF Term Γ) {t : SF Term Γ} → Redex t → Redex (app f t)
  [lam]    : {b : SF Term (Term ∷ Γ)} → Redex b → Redex (lam b)
  [App]    : {f : SF Term Γ} → Redex f → (t : SF Type Γ) → Redex (App f t)
  [Lam]    : {b : SF Term (Type ∷ Γ)} → Redex b → Redex (Lam b)

open import Category.Monad
open import Data.Maybe
open import Data.Maybe.Categorical
import Level
open RawMonadPlus (monadPlus {Level.zero})

redex : {Γ : List Kind} (t : SF Term Γ) → Maybe (Redex t)
redex (app (lam b) u) = just (applam b u)
redex (App (Lam b) u) = just (AppLam b u)
redex (app f t)       = flip [app-l] t <$> redex f ∣ [app-r] f <$> redex t
redex (lam b)         = [lam] <$> redex b
redex (App f t)       = flip [App] t <$> redex f
redex (Lam b)         = [Lam] <$> redex b
redex _ = nothing

fire : {Γ : List Kind} {t : SF Term Γ} → Redex t → SF Term Γ
fire (applam b u)  = sub (base vl^Tm ∙ u) b
fire (AppLam b u)  = sub (base vl^Tm ∙ u) b
fire ([app-l] f t) = app (fire f) t
fire ([app-r] f t) = app f (fire t)
fire ([lam] b)     = lam (fire b)
fire ([App] f t)   = App (fire f) t
fire ([Lam] b)     = Lam (fire b)

open import Codata.Thunk
open import Codata.Colist
open import Codata.Colist.Bisimilarity using (_⊢_≈_; _∷_; [])


eval : ∀ {i} (Γ : List Kind) (t : SF Term Γ) → Colist (SF Term Γ) i
eval Γ t with redex t
... | just r  = t ∷ λ where .force → eval Γ (fire r)
... | nothing = t ∷ λ where .force → []

`id : SF Term []
`id = Lam (lam (`var z))

_ : _ ⊢ eval [] (lam (lam (app (lam (app (`var z) (`var z))) (lam (`var z)))))
  ≈ fromList (_ ∷ _ ∷ lam (lam (lam (`var z))) ∷ [])
_ = refl ∷ λ where .force → refl ∷ λ where .force → refl ∷ λ where .force → []
\end{code}

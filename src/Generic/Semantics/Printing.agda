module Generic.Semantics.Printing where

open import Coinduction
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Nat.Base
open import Data.Nat.Show as Nat
open import Data.List.Base as L hiding ([_] ; _++_ ; lookup)
open import Data.Char
open import Data.String using (String ; _++_ ; fromList ; toList)
open import Data.Stream as Str hiding (_++_ ; lookup)
open import Category.Monad
open import Category.Monad.State
open import Function


-- The Printing Monad we are working with: a state containing a stream
-- of *distinct* Strings.
open module ST = RawMonadState (StateMonadState (Stream String))
M = State (Stream String)

open import var hiding (get)
open import environment as E
open import varlike
open import Generic.Syntax as S
open import Generic.Semantics

-- First we use some wrappers with phantom indices for the type of
-- Values and Computations of our Semantics

module _ {I : Set} where

  record Name (i : I) (Γ : List I) : Set where
    constructor mkN; field getN : String
  open Name public

  record Printer (i : I) (Γ : List I) : Set where
    constructor mkP; field getP : M String
  open Printer public

-- We define a handy combinator to generate fresh Names (and make sure
-- they are dropped from the state)

module _ {I : Set} where

  fresh : {i : I} {Γ : List I} → M (Name i Γ)
  fresh =  get             >>=  λ nms  →
           put (tail nms)  >>=  λ _    →
           return $ mkN $ head nms

-- Names are varlike in the monad M: we use the state to generate fresh
-- ones. Closure under thinning is a matter of wrapping / unwrapping the
-- name.

  vl^StName : VarLike (λ i Γ → State (Stream String) (Name i Γ))
  new   vl^StName = fresh
  th^𝓥 vl^StName = λ st _ → mkN ∘ getN ST.<$> st


-- To print a term the user need to explain to us how to display one
-- layer of term given that the newly-bound variables have been assigned
-- fresh names and the subterms have already been rendered using these
-- names.

module _ {I : Set} (d : Desc I) where

  Pieces : List I → I ─Scoped
  Pieces []  i Γ = String
  Pieces Δ   i Γ = (Δ ─Env) (λ _ _ → String) [] × String

  record Display : Set where
    constructor mkD
    field getD : ∀ {i Γ} → ⟦ d ⟧ Pieces i Γ → String
  open Display public

---------------------------------------------------------------------
-- Generic Printing Semantics

-- Given a strategy to `Display` one layer of term we can generate a full
-- printer.

module _ {I : Set} {d : Desc I} where

  printing : Display d → Sem d Name Printer
  Sem.th^𝓥 (printing dis)        n = const $ mkN (getN n)
  Sem.var  (printing dis)         n = mkP (return (getN n))
  Sem.alg  (printing dis) {i} {Γ} v = mkP $ getD dis ST.<$> ih where

    reify^M : {Γ : List I} (Δ : List I) (i : I) →
              Kripke Name Printer Δ i Γ →
              M (Pieces d Δ i Γ)
    reify^M []         i = getP
    reify^M Δ@(_ ∷ _)  i = λ f → let σ = freshˡ vl^StName _
                                in  E.traverse rawIApplicative σ >>= λ ρ →
                                    getP (f (freshʳ vl^Var Δ) ρ) >>= λ b →
                                    return ((getN E.<$> ρ) , b)

    ih : M (⟦ d ⟧ (Pieces d) i Γ)
    ih = S.traverse rawIApplicative d (fmap d reify^M v)

-- Corollary: a generic printer using a silly name supply

  print : Display d → {i : I} → TM d i → String
  print dis t = proj₁ $ getP (Sem.closed (printing dis) t) names where

   flatten : {A : Set} → Stream (A × List A) → Stream A
   flatten ((a , as) Str.∷ aass) = go a as (♭ aass) where
     go : {A : Set} → A → List A → Stream (A × List A) → Stream A
     go a []        aass = a ∷ ♯ flatten aass
     go a (b ∷ as)  aass = a ∷ ♯ go b as aass

   names : Stream String
   names = flatten $ Str.zipWith cons letters
                  $ "" ∷ ♯ Str.map Nat.show (allNatsFrom 0)
    where

      cons : (Char × List Char) → String → (String × List String)
      cons (c , cs) suffix = appendSuffix c , L.map appendSuffix cs where
        appendSuffix : Char → String
        appendSuffix c  = fromList (c ∷ []) ++ suffix

      letters = Str.repeat $ 'a' , toList "bcdefghijklmnopqrstuvwxyz"

      allNatsFrom : ℕ → Stream ℕ
      allNatsFrom k = k ∷ ♯ allNatsFrom (1 + k)

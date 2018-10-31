module Generic.Semantics.Printing where

open import Codata.Thunk
open import Codata.Stream as Stream using (Stream; _∷_)

open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Nat.Base
open import Data.Nat.Show as Nat
open import Data.List.Base using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Char
open import Data.String using (String ; _++_ ; fromList ; toList)
open import Category.Monad
open import Category.Monad.State
open import Function


-- The Printing Monad we are working with: a state containing a stream
-- of *distinct* Strings.
open module ST = RawMonadState (StateMonadState (Stream String _))
M = State (Stream String _)

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
  fresh =  get                    >>=  λ nms  →
           put (Stream.tail nms)  >>=  λ _    →
           return $ mkN $ Stream.head nms

-- Names are varlike in the monad M: we use the state to generate fresh
-- ones. Closure under thinning is a matter of wrapping / unwrapping the
-- name.

  vl^StName : VarLike (λ i Γ → M (Name i Γ))
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

    alphabetWithSuffix : String → List⁺ String
    alphabetWithSuffix suffix = List⁺.map (λ c → fromList (c ∷ []) ++ suffix)
                              $′ 'a' ∷ toList "bcdefghijklmnopqrstuvwxyz"

    allNats : Stream ℕ _
    allNats = cofix (λ i → ℕ → Stream ℕ i) step 0 where
      step : ∀ {i} → Thunk _ i → ℕ → Stream ℕ i
      step rec k = k ∷ λ where .force → rec .force (suc k)

    names : Stream String _
    names = Stream.concat
          $′ Stream.map alphabetWithSuffix
          $′ "" ∷ λ where .force → Stream.map Nat.show allNats

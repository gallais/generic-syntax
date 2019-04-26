\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Semantics.Printing where

open import Size
open import Codata.Thunk using (Thunk; force)
open import Codata.Stream using (Stream; _∷_; head; tail; map; concat; iterate)
open import Data.Unit
open import Data.Bool
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Nat.Base
open import Data.Nat.Show as Nat
open import Data.List.Base using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Char using (Char)
open import Data.String using (String ; _++_ ; toList; fromList)
open import Category.Monad
open import Category.Monad.State
open import Function

module ST = RawMonadState (StateMonadState (Stream String ∞))

M = State (Stream String ∞)

instance
 _ = ST.rawIApplicative

open import Data.Var hiding (get)
open import Data.Environment as E
open import Data.Var.Varlike
open import Generic.Syntax as S
open import Generic.Semantics

module _ {I : Set} where

 record Name (i : I) (Γ : List I) : Set where
   constructor mkN; field getN : String

 record Printer (i : I) (Γ : List I) : Set where
   constructor mkP; field getP : M String

open Name
open Printer

module _ {I : Set} where

 fresh : {i : I} {Γ : List I} → M (Name i Γ)
 fresh =  get             >>=  λ nms  →
          put (tail nms)  >>=  λ _    →
          return $ mkN $ head nms
   where open ST

module _ {I : Set} (d : Desc I) where

 Pieces : List I → I ─Scoped
 Pieces []  i Γ = String
 Pieces Δ   i Γ = (Δ ─Env) (λ _ _ → String) [] × String

 record Display : Set where
   constructor mkD
   field getD : ∀ {i Γ} → ⟦ d ⟧ Pieces i Γ → String

open Display public

module _ {I : Set} {d : Desc I} where

 printing : Display d → Semantics d Name Printer
 printing dis = record
   { th^𝓥  = λ n _ → mkN (getN n)
   ; var   = λ n → mkP (return (getN n))
   ; alg   = λ {i} {Γ} v → mkP
           $ let p : M (⟦ d ⟧ (Pieces d) i Γ)
                 p = S.sequenceA d (fmap d reify^M v)
             in getD dis ST.<$> p
   } where
   open ST

   vl^StName : VarLike {I} (λ i Γ → M (Name i Γ))
   vl^StName = record
     { new   = fresh
     ; th^𝓥  = λ st _ → mkN ∘ getN ST.<$> st }

   reify^M : {Γ : List I} (Δ : List I) (i : I) →
             Kripke Name Printer Δ i Γ →
             M (Pieces d Δ i Γ)
   reify^M []         i = getP
   reify^M Δ@(_ ∷ _)  i = λ f → let open ST in do
     let σ = freshˡ vl^StName _
     ρ ← E.sequenceA σ
     b ← getP (f (freshʳ vl^Var Δ) ρ)
     return ((getN E.<$> ρ) , b)


 print : Display d → {i : I} → Tm d ∞ i [] → String
 print dis t = proj₁ $ getP (Semantics.closed (printing dis) t) names where

  letters : List⁺ String
  letters = List⁺.map (fromList ∘ (_∷ []))
          $ 'a' ∷ toList "bcdefghijklmnopqrst"

  names : Stream String ∞
  names = concat
        $ map (λ suff → List⁺.map (_++ suff) letters)
        $ "" ∷ λ where .force → map show (iterate suc zero)
\end{code}

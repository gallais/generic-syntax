\begin{code}
module Generic.Examples.Printing where

open import Size
open import Coinduction hiding (∞)
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Nat.Base
open import Data.Nat.Show as Nat
open import Data.List.Base as L hiding ([_] ; _++_)
open import Data.Char
open import Data.String using (String ; _++_ ; fromList ; toList)
open import Data.Stream as Str hiding (_++_ ; lookup)
open import Category.Monad
open import Category.Monad.State
open import Function

module ST = RawMonadState (StateMonadState (Stream String))
open ST

M = State (Stream String)

open import var hiding (get)
open import environment as E hiding (refl)
open import varlike
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

module _ {I : Set} (d : Desc I) where

 Pieces : List I → I ─Scoped
 Pieces []  i Γ = String
 Pieces Δ   i Γ = (Δ ─Env) (λ _ _ → String) [] × String

 record Display : Set where
   constructor mkD
   field getD : ∀ {i Γ} → ⟦ d ⟧ Pieces i Γ → String

open Display

module _ {I : Set} {d : Desc I} where

 printing : Display d → Sem d Name Printer
 printing dis = record
   { th^𝓥  = λ n _ → mkN (getN n)
   ; var   = λ n → mkP (return (getN n))
   ; alg   = λ {i} {Γ} v → mkP
           $ let p : M (⟦ d ⟧ (Pieces d) i Γ)
                 p = S.traverse rawIApplicative d (fmap d reify^M v)
             in getD dis ST.<$> p
   } where

   vl^StName : VarLike {I} (λ i Γ → State (Stream String) (Name i Γ))
   vl^StName = record
     { new   = fresh
     ; th^𝓥  = λ st _ → mkN ∘ getN ST.<$> st }

   reify^M : {Γ : List I} (Δ : List I) (i : I) →
             Kripke Name Printer Δ i Γ →
             M (Pieces d Δ i Γ)
   reify^M []         i = getP
   reify^M Δ@(_ ∷ _)  i = λ f → let σ = freshˡ vl^StName _
                                in  E.traverse rawIApplicative σ >>= λ ρ →
                                    getP (f (freshʳ vl^Var Δ) ρ) >>= λ b →
                                    return ((getN E.<$> ρ) , b)

 print : Display d → {i : I} → Tm d ∞ i [] → String
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


open import Generic.Examples.UntypedLC

printLC : Display LCD
getD printLC = case (λ { (f , t , _)    → f ++ "(" ++ t ++ ")" })
                    (λ { ((x , b) , _)  → "λ" ++ lookup x z ++ ". " ++ b })

open import Agda.Builtin.Equality

_ : print printLC `id ≡ "λa. a"
_ = refl

open import Generic.Examples.HuttonsRazor

printHR : Display HuttRaz
getD printHR = case (Nat.show ∘ proj₁)
                    (λ { (m , n , _) → m ++ " + " ++ n })

_ : print printHR ((lit 2 [+] lit 6) [+] lit 0) ≡ "2 + 6 + 0"
_ = refl

open import Generic.Examples.SystemF as SystemF

printSF : Display system-F
getD printSF  = case  (λ { (σ , τ , _)    → σ ++ " → " ++ τ })
              $ case  (λ { ((x , b) , _)  → "∀" ++ lookup x z ++ ". " ++ b })
              $ case  (λ { (f , t , _)    → f ++ "(" ++ t ++ ")" })
              $ case  (λ { ((x , b) , _)  → "λ" ++ lookup x z ++ ". " ++ b })
              $ case  (λ { (f , T , _)    → f ++ "(" ++ T ++ ")" })
                      (λ { ((x , b) , _)  → "Λ" ++ lookup x z ++ ". " ++ b })

_ : print printSF SystemF.`id ≡ "Λa. λb. b"
_ = refl
\end{code}

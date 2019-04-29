\begin{code}
module Generic.Semantics.Printing {I : Set} where

open import Codata.Thunk using (Thunk; force)
open import Codata.Stream as Stream using (Stream; _∷_)

open import Data.Product
open import Data.Nat.Base
open import Data.Nat.Show as Nat
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Char
open import Data.String using (String ; fromList ; toList)
open import Category.Monad
open import Category.Monad.State
open import Function
open import Relation.Unary

-- We reuse Name, Printer, M, fresh, and names from the STLC printing example

open import StateOfTheArt.ACMM using (module Printer)
open Printer using (M; Wrap; MkW; getW; map^Wrap; th^Wrap; fresh; names)

private
  variable
    Γ Δ : List I
    σ : I

-- The Printing Monad we are working with: a state containing a stream
-- of *distinct* Strings.
module ST = RawMonadState (StateMonadState (Stream String _))
open ST renaming (rawIApplicative to ApplicativeM)
        hiding (_<$>_)

open import Data.Var hiding (get; _<$>_)
open import Data.Environment hiding (_>>_; sequenceA; _<$>_)
open import Data.Var.Varlike
open import Generic.Syntax hiding (sequenceA)
open import Generic.Semantics

Name Printer : I ─Scoped
Name    = Wrap String
Printer = Wrap (M String)


vl^MName : VarLike (λ σ Γ → M (Name σ Γ))
th^𝓥  vl^MName = λ mn ρ → (λ n → th^Wrap n ρ) ST.<$> mn
new   vl^MName = fresh _

-- To print a term the user need to explain to us how to display one
-- layer of term given that the newly-bound variables have been assigned
-- fresh names and the subterms have already been rendered using these
-- names.

\end{code}
%<*pieces>
\begin{code}
Pieces : List I → I ─Scoped
Pieces []  i Γ = String
Pieces Δ   i Γ = (Δ ─Env) Name (Δ ++ Γ) × String
\end{code}
%</pieces>
%<*reifypieces>
\begin{code}
reify^M : ∀ Δ i → Kripke Name Printer Δ i Γ → M (Pieces Δ i Γ)
reify^M []         i p  = getW p
reify^M Δ@(_ ∷ _)  i f  = do
  ρ ← sequenceA (freshˡ vl^MName _)
  b ← getW (f (freshʳ vl^Var Δ) ρ)
  return (ρ , b)
\end{code}
%</reifypieces>
\begin{code}
  where open Data.Environment
        instance _ = ApplicativeM

\end{code}
%<*display>
\begin{code}
Display : Desc I → Set
Display d = ∀ {i Γ} → ⟦ d ⟧ Pieces i Γ → String
\end{code}
%</display>
\begin{code}

---------------------------------------------------------------------
-- Generic Printing Semantics

-- Given a strategy to `Display` one layer of term we can generate a full
-- printer.

open Semantics

module _ {d : Desc I} where

\end{code}
%<*printing>
\begin{code}
  printing : Display d → Semantics d Name Printer
  printing dis .th^𝓥  = th^Wrap
  printing dis .var   = map^Wrap return
  printing dis .alg   = λ v → MkW $ dis <$> sequenceA d (fmap d reify^M v)
\end{code}
%</printing>
\begin{code}
    where open Generic.Syntax
          open ST
          instance _ = ApplicativeM

-- Corollary: a generic printer using a silly name supply

\end{code}
%<*print>
\begin{code}
  print : Display d → TM d σ → String
  print dis t = proj₁ $ getW (closed (printing dis) t) names
\end{code}
%</print>
\begin{code}

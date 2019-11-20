\begin{code}
{-# OPTIONS --safe --sized-types #-}

open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality

open import Generic.Syntax

module Generic.Scopecheck {E I : Set} (_≟I_ : Decidable {A = I} _≡_) where

open import Category.Monad

open import Level
open import Size
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties
  using () renaming (++⁺ to _++_)

open import Data.Product
open import Data.String using (String; _≟_)
open import Data.Sum
import Data.Sum.Categorical.Left as SC
open import Function
open import Relation.Nullary

open import Data.Var hiding (_<$>_)

private
  variable
    σ : I
    Γ Δ : List I
    i : Size
    A : Set

\end{code}
%<*names>
\begin{code}
Names : List I → Set
Names = All (const String)
\end{code}
%</names>
%<*withnames>
\begin{code}
WithNames : (I → Set) → List I → I ─Scoped
WithNames T []  j Γ = T j
WithNames T Δ   j Γ = Names Δ × T j
\end{code}
%</withnames>
%<*raw>
\begin{code}
data Raw (d : Desc I) : Size → I → Set where
  `var  : E → String → Raw d (↑ i) σ
  `con  : ⟦ d ⟧ (WithNames (Raw d i)) σ [] → Raw d (↑ i) σ
\end{code}
%</raw>
\begin{code}

\end{code}
%<*error>
\begin{code}
data Error : Set where
  OutOfScope  : Error
  WrongSort   : (σ τ : I) → σ ≢ τ → Error
\end{code}
%</error>
\begin{code}

private
\end{code}
%<*monad>
\begin{code}
 Fail : Set → Set
 Fail A = (Error × E × String) ⊎ A
\end{code}
%</monad>
%<*fail>
\begin{code}
 fail : Error → E → String → Fail A
 fail err e str = inj₁ (err , e , str)
\end{code}
%</fail>
\begin{code}
open RawMonad (SC.monad (Error × E × String) zero)

instance _ =  rawIApplicative

\end{code}
%<*toVar>
\begin{code}
toVar : E → String → ∀ σ Γ → Names Γ → Fail (Var σ Γ)
toVar e x σ [] [] = fail OutOfScope e x
toVar e x σ (τ ∷ Γ) (y ∷ scp) with x ≟ y | σ ≟I τ
... | yes _  | yes refl  = pure z
... | yes _  | no ¬eq    = fail (WrongSort σ τ ¬eq) e x
... | no ¬p  | _         = s <$> toVar e x σ Γ scp
\end{code}
%</toVar>
\begin{code}
module _ {d : Desc I} where
\end{code}
%<*scopecheck>
\begin{AgdaAlign}
\begin{AgdaSuppressSpace}
%<*totmtype>
\begin{code}
 toTm     : Names Γ → Raw d i σ → Fail (Tm d i σ Γ)
\end{code}
%</totmtype>
\begin{code}
 toScope  : Names Γ → ∀ Δ σ → WithNames (Raw d i) Δ σ [] → Fail (Scope (Tm d i) Δ σ Γ)

 toTm scp (`var e v)  = `var <$> toVar e v _ _ scp
 toTm scp (`con b)    = `con <$> mapA d (toScope scp) b

 toScope scp []         σ b          = toTm scp b
 toScope scp Δ@(_ ∷ _)  σ (bnd , b)  = toTm (bnd ++ scp) b
\end{code}
\end{AgdaSuppressSpace}
\end{AgdaAlign}
%</scopecheck>

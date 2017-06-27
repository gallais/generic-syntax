\begin{code}
module Generic.Examples.ElaborationType where

open import Size
open import Function
open import Data.Bool
open import Data.Product as P hiding (,_)
open import Data.List hiding ([_])
open import Data.List.All as All hiding (lookup)
open import Data.Maybe as Maybe hiding (All)


open import indexed
open import var hiding (_<$>_)
open import environment hiding (refl ; _<$>_)
open import Generic.Syntax
open import Generic.Semantics

import Category.Monad as CM
import Level
module M = CM.RawMonad (Maybe.monad {Level.zero})
open M

open import Relation.Binary.PropositionalEquality hiding ([_])

erase^All : {A B : Set} {xs : List A} → All (const B) xs → List B
erase^All []        = []
erase^All (b ∷ bs)  = b ∷ erase^All bs

infixr 5 _⇒_
data Type : Set where
  α    : Type
  _⇒_  : Type → Type → Type

infix 3 _==_
_==_ : (σ τ : Type) → Maybe (σ ≡ τ)
α     == α       = just refl
σ ⇒ τ == σ' ⇒ τ' = uncurry (cong₂ _⇒_) <$> ((σ == σ') ⊗ (τ == τ'))
_     == _       = nothing

isArrow : (σ⇒τ : Type) → Maybe (∃ λ στ → σ⇒τ ≡ uncurry _⇒_ στ)
isArrow (σ ⇒ τ) = just ((σ , τ) , refl)
isArrow _       = nothing
\end{code}
%<*bidirectional>
\begin{code}
data Phase : Set where Check Infer : Phase

Lang : Desc Phase
Lang  =   `X [] Infer (`X [] Check (`∎ Infer))    -- apply
      `+  `X (Infer ∷ []) Check (`∎ Check)        -- lamda
      `+  `σ Type (λ _ → `X [] Check (`∎ Infer))  -- cut
      `+  `X [] Infer (`∎ Check)                  -- embed
\end{code}
%<*langsyntax>
\begin{code}
pattern `app f t  = `con (true , f , t , refl)
pattern `lam b    = `con (false , true , b , refl)
pattern `cut σ t  = `con (false , false , true , σ , t , refl)
pattern `emb t    = `con (false , false , false , t , refl)
\end{code}
%</langsyntax>
\begin{code}
Elab : Desc Type
Elab  =   `σ Type (λ σ → `σ Type (λ τ → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ))))  -- app
      `+  `σ Type (λ σ → `σ Type (λ τ → `X (σ ∷ []) τ (`∎ (σ ⇒ τ))))      -- lam
\end{code}
%</bidirectional>
%<*elabsyntax>
\begin{code}
pattern `app^E f t  = `con (true , _ , _ , f , t , refl)
pattern `lam^E b    = `con (false , _ , _ , b , refl)
\end{code}
%</elabsyntax>

%<*typemode>
\begin{code}
Type- : Phase → List Phase → Set
Type- Check  Γ = (γ : All (const Type) Γ) (σ : Type)  → Maybe (Tm Elab ∞ σ (erase^All γ))
Type- Infer  Γ = (γ : All (const Type) Γ)             → Maybe (∃ λ σ → Tm Elab ∞ σ (erase^All γ))

Var- : Phase → List Phase → Set
Var- _ Γ = (γ : All (const Type) Γ) → ∃ λ σ → Var σ (erase^All γ)
\end{code}
%</typemode>
%<*typecheck>
\begin{code}
Typecheck : Sem Lang Var- Type-
Sem.th^𝓥  Typecheck = λ v ρ γ → let (σ , x) = v (rewind _ γ ρ) in σ , unwind _ γ ρ x where

  rewind : (Γ : List Phase) {Δ : List Phase} → All (const Type) Δ → Thinning Γ Δ → All (const Type) Γ
  rewind []       σs th = []
  rewind (σ ∷ Γ)  σs th = get (lookup th z) σs ∷ (rewind Γ σs (select extend th))

  got : {Δ : List Phase} {p : Phase} (k : Var p Δ) (γ : All (const Type) Δ) → Var (get k γ) (erase^All γ)
  got z     (σ ∷ _) = z
  got (s k) (_ ∷ γ) = s (got k γ)

  unwind : (Γ : List Phase) {Δ : List Phase} {σ : Type} (γ : All (const Type) Δ) (ρ : Thinning Γ Δ) → 
           Var σ (erase^All (rewind Γ γ ρ)) → Var σ (erase^All γ)
  unwind [] γ ρ ()
  unwind (σ ∷ Γ) γ ρ z     = got (lookup ρ z) γ
  unwind (σ ∷ Γ) γ ρ (s v) = unwind Γ γ (select extend ρ) v

Sem.var    Typecheck {i} = var i

  where

   var : (i : Phase) → [ Var- i ⟶ Type- i ]
   var Check v γ σ  = let (τ , x) = v γ
                          cast    = flip (subst (λ σ → Var σ (erase^All γ)) ∘ sym)
                       in `var ∘ cast x <$> (σ == τ)
   var Infer v γ    = let (τ , x) = v γ
                      in just (τ , `var x)

Sem.alg    Typecheck = case app $ case lam $ case cut emb
\end{code}
%</typecheck>
\begin{code}
  where

   app : {i : Phase} → [ Type- Infer ∙× Type- Check ∙× κ (i ≡ Infer) ⟶ Type- i ]
   app (f , t , refl) γ =  f γ          >>= λ { (σ⇒τ , F) →
                           isArrow σ⇒τ  >>= λ { ((σ , τ) , refl) →
                           t γ σ        >>= λ T →
                           return (τ , `app^E F T) } }

   lam : {i : Phase} → [ □ (((Infer ∷ [] ─Env) Var-) ⟶ Type- Check) ∙× κ (i ≡ Check) ⟶ Type- i ]
   lam {i} {Γ} (b , refl) γ σ⇒τ =
     isArrow σ⇒τ >>= λ { ((σ , τ) , refl) →
     let inc : Thinning Γ (Infer ∷ Γ)
         inc = extend
         val : (Infer ∷ [] ─Env) Var- (Infer ∷ Γ)
         val = ε ∙ (λ { (σ ∷ γ) → (σ , z) })
     in `lam^E <$> b inc val (σ ∷ γ) τ }

   cut : {i : Phase} → [ κ Type ∙× Type- Check ∙× κ (i ≡ Infer) ⟶ Type- i ]
   cut (σ , t , refl) γ = (σ ,_) <$> t γ σ

   emb : {i : Phase} → [ Type- Infer ∙× κ (i ≡ Check) ⟶ Type- i ]
   emb (t , refl) γ σ =  t γ     >>= λ { (τ , T) →
                         σ == τ  >>= λ { refl →
                         return T } }
\end{code}
\begin{code}
type- : (p : Phase) → Tm Lang ∞ p [] → Type- p []
type- p t = Sem.sem Typecheck {Δ = []} ε t

_ : let  id  : Tm Lang ∞ Check []
         id  = `lam (`emb (`var z))
    in type- Infer (`app (`cut ((α ⇒ α) ⇒ (α ⇒ α)) id) id) []
     ≡ just (α ⇒ α , `app^E (`lam^E (`var z)) (`lam^E (`var z)))
_ = refl
\end{code}

\begin{code}
module generic-syntax where

open import Level using (Level)
open import Size
open import Data.Bool
open import Data.List.Base as L hiding ([_])
open import Data.List.All using (All ; [] ; _∷_)
open import Data.Unit
open import Data.Sum as Sum
open import Data.Product as Prod hiding (,_)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import var
open import indexed 
open import environment as E hiding (refl)

\end{code}
%<*desc>
\begin{code}
data Desc (I : Set) : Set₁ where
  `σ : (A : Set) (d : A → Desc I)  → Desc I
  `X : List I → I → Desc I         → Desc I
  `∎ : I                            → Desc I
\end{code}
%</desc>
\begin{code}
module _ {I : Set} where

 infixr 5 _`+_

 `K : Set → I → Desc I
 `K A i = `σ A (λ _ → `∎ i)


\end{code}
%<*sumcomb>
\begin{code}
 _`+_ : Desc I → Desc I → Desc I
 d `+ e =  `σ Bool $ λ isLeft →
           if isLeft then d else e
\end{code}
%</sumcomb>
%<*paircomb>
\begin{code}
 `Xs : List I → I → I → Desc I
 `Xs js j i = foldr (`X []) (`X js j (`∎ i)) js
\end{code}
%</paircomb>
%<*interp>
\begin{code}
⟦_⟧ : {I : Set} → Desc I → (List I → I → List I → Set) → (I → List I → Set)
⟦ `σ A d    ⟧ X i Γ = Σ[ a ∈ A ] (⟦ d a ⟧ X i Γ)
⟦ `X Δ j d  ⟧ X i Γ = X Δ j Γ × ⟦ d ⟧ X i Γ
⟦ `∎ i′     ⟧ X i Γ = i ≡ i′
\end{code}
%</interp>
\begin{code}

module _ {I : Set} {X : List I → I → List I → Set} {i j k : I} {Γ : List I} where
\end{code}
%<*pairunpair>
\begin{code}
 unXs :  (Δ : List I) → ⟦ `Xs Δ j i ⟧ X k Γ → All (λ i → X [] i Γ) Δ × X Δ j Γ × k ≡ i
\end{code}
%</pairunpair>
\begin{code}
 unXs = go id where

  go : (f : List I → List I) → (Δ : List I) →
       ⟦ foldr (`X []) (`X (f Δ) j (`∎ i)) Δ ⟧ X k Γ → All (λ i → X [] i Γ) Δ × X (f Δ) j Γ × k ≡ i
  go f []       (v , eq) = [] , v , eq
  go f (σ ∷ Δ)  (t , v)  = Prod.map (t ∷_) id $ go (f ∘ (σ ∷_)) Δ v
\end{code}
%<*case>
\begin{code}
case : {I : Set} {d e : Desc I} {X : List I → I → List I → Set} {A : Set} {i : I} {Γ : List I} →
  (⟦ d       ⟧ X i Γ → A) → (⟦ e       ⟧ X i Γ → A) → (⟦ d `+ e  ⟧ X i Γ → A)
\end{code}
%</case>
\begin{code}
case l r (true   , t) = l t
case l r (false  , t) = r t

fmap : {I : Set} (d : Desc I) {X Y : List I → I → List I → Set}
       {Γ Δ : List I} {i : I} → (∀ Θ i → X Θ i Γ → Y Θ i Δ) → ⟦ d ⟧ X i Γ → ⟦ d ⟧ Y i Δ
fmap (`σ A d)   f = Prod.map id (fmap (d _) f)
fmap (`X Δ j d) f = Prod.map (f Δ j) (fmap d f)
fmap (`∎ i)     f = id

\end{code}
%<*scope>
\begin{code}
Scope : {I : Set} (T : I → List I → Set) → (List I → I → List I → Set)
Scope T Δ i = (Δ ++_) ⊢ T i
\end{code}
%</scope>
%<*mu>
\begin{code}
data Tm {I : Set} (d : Desc I) : Size → I → List I → Set where
  `var : {s : Size} {i : I} →  [ Var i                    ⟶ Tm d (↑ s) i ]
  `con : {s : Size} {i : I} →  [ ⟦ d ⟧ (Scope (Tm d s)) i ⟶ Tm d (↑ s) i ]
\end{code}
%</mu>

%<*LCD>
\begin{code}
LCD : Desc ⊤
LCD =  `σ Bool $ λ isApp → if isApp
       then `X [] tt (`X [] tt (`∎ tt))
       else `X (tt ∷ []) tt (`∎ tt)
\end{code}
%</LCD>
%<*LC>
\begin{code}
LC : List ⊤ → Set
LC = Tm LCD ∞ tt
\end{code}
%</LC>
%<*var>
\begin{code}
`V : [ Var tt ⟶ LC ]
`V = `var
\end{code}
%</var>
%<*app>
\begin{code}
`A : [ LC ⟶ LC ⟶ LC ]
`A f t = `con (true , f , t , refl)
\end{code}
%</app>
%<*lam>
\begin{code}
`L : [ (tt ∷_) ⊢ LC ⟶ LC ]
`L b = `con (false , b , refl)
\end{code}
%</lam>

%<*semantics>
\begin{code}
Alg : {I : Set} (d : Desc I) (𝓥 𝓒 : I → List I → Set) → Set
Alg {I} d 𝓥 𝓒 = {i : I} → [ ⟦ d ⟧ (Kripke 𝓥 𝓒) i ⟶ 𝓒 i ]

record Sem {I : Set} (d : Desc I) (𝓥 𝓒 : I → List I → Set) : Set where
  field  th^𝓥   : {i : I} → Thinnable (𝓥 i)
         var    : {i : I} → [ 𝓥 i                  ⟶ 𝓒 i ]
         alg    : Alg d 𝓥 𝓒
\end{code}
%</semantics>

%<*sembody>
\begin{code}
  _─Comp : (Γ : List I) (𝓒 : I → List I → Set) (Δ : List I) → Set
  (Γ ─Comp) 𝓒 Δ = {s : Size} {i : I} → Tm d s i Γ → 𝓒 i Δ

  sem   : {Γ Δ : List I} → (Γ ─Env) 𝓥 Δ → (Γ ─Comp) 𝓒 Δ
  body  :  {Γ Δ : List I} {s : Size} → (Γ ─Env) 𝓥 Δ →
           ∀ Θ i → Scope (Tm d s) Θ i Γ → Kripke 𝓥 𝓒 Θ i Δ
\end{code}
%</sembody>
%<*sem>
\begin{code}
  sem ρ (`var k) = var (lookup ρ k)
  sem ρ (`con t) = alg (fmap d (body ρ) t)
\end{code}
%</sem>
%<*body>
\begin{code}
  body ρ []       i t = sem ρ t
  body ρ (_ ∷ _)  i t = λ ren vs → sem (vs >> th^Env th^𝓥 ρ ren) t
\end{code}
%</body>
%<*varlike>
\begin{code}

record VarLike {I : Set} (𝓥 : I → List I → Set) : Set where
  field  new   : {i : I} → [ (i ∷_) ⊢ 𝓥 i ]
         th^𝓥  : {i : I} → Thinnable (𝓥 i)
\end{code}
%</varlike>
\begin{code}
  base : ∀ {Γ} → (Γ ─Env) 𝓥 Γ
  base {[]}  = ε
  base {σ ∷ Γ} = th^Env th^𝓥 base extend ∙ new

  freshʳ : (Δ : List I) → ∀ {Γ} → (Γ ─Env) 𝓥 (Δ ++ Γ)
  freshʳ Δ = th^Env th^𝓥 base (pack (injectʳ Δ))

  freshˡ : (Δ : List I) → ∀ {Γ} → (Γ ─Env) 𝓥 (Γ ++ Δ)
  freshˡ k = th^Env th^𝓥 base (pack (injectˡ _))
open VarLike public

vl^Var : {I : Set} → VarLike {I} Var
vl^Var = record
  { new    = z
  ; th^𝓥  = th^Var
  }
\end{code}
%<*reify>
\begin{code}
reify : {I : Set} {𝓥 𝓒 : I → List I → Set} → VarLike 𝓥 →
        {Γ : List I} → ∀ Δ i → Kripke 𝓥 𝓒 Δ i Γ → Scope 𝓒 Δ i Γ
reify vl^𝓥 []        i b = b
reify vl^𝓥 Δ@(_ ∷ _) i b = b (freshʳ vl^Var Δ) (freshˡ vl^𝓥 _)
\end{code}
%</reify>
\begin{code}

record Syntactic {I : Set} (d : Desc I) (𝓥 : I → List I → Set) : Set where
  field
    var    : {i : I} → [ 𝓥 i ⟶ Tm d ∞ i ]
    vl^𝓥  : VarLike 𝓥

  semantics : Sem d 𝓥 (Tm d ∞)
  semantics = record
    { var   = var
    ; th^𝓥 = th^𝓥 vl^𝓥
    ; alg   = `con ∘ alg' d
    } where

    alg' : {i : I} → ∀ e → [ ⟦ e ⟧ (Kripke 𝓥 (Tm d ∞)) i ⟶ ⟦ e ⟧ (Scope (Tm d ∞)) i ]
    alg' e = fmap e (λ Θ i → reify vl^𝓥 Θ i)

sy^Var : {I : Set} {d : Desc I} → Syntactic d Var
sy^Var = record
  { var    = `var
  ; vl^𝓥  = vl^Var
  }
\end{code}
%<*renaming>
\begin{code}
Renaming : {I : Set} (d : Desc I) → Sem d Var (Tm d ∞)
Sem.th^𝓥  (Renaming d) = λ k ρ → lookup ρ k
Sem.var   (Renaming d) = `var
Sem.alg   (Renaming d) = `con ∘ fmap d (reify vl^Var)

ren :  {I : Set} {Γ Δ : List I} {i : I} → ∀ d → (Γ ─Env) Var Δ →
       Tm d ∞ i Γ → Tm d ∞ i Δ
ren d ρ t = Sem.sem (Renaming d) ρ t
\end{code}
%</renaming>
\begin{code}
th^Tm : {I : Set} {d : Desc I} {i : I} → Thinnable (Tm d ∞ i)
th^Tm t ρ = Sem.sem (Renaming _) ρ t

vl^Tm : {I : Set} {d : Desc I} → VarLike (Tm d ∞)
new   vl^Tm = `var z
th^𝓥  vl^Tm = th^Tm

sy^Tm : {I : Set} {d : Desc I} → Syntactic d (Tm d ∞)
Syntactic.var   sy^Tm = id
Syntactic.vl^𝓥  sy^Tm = vl^Tm

\end{code}
%<*substitution>
\begin{code}
Substitution : {I : Set} (d : Desc I) → Sem d (Tm d ∞) (Tm d ∞)
Sem.th^𝓥  (Substitution d) = λ t ρ → Sem.sem (Renaming d) ρ t
Sem.var   (Substitution d) = id
Sem.alg   (Substitution d) = `con ∘ fmap d (reify vl^Tm)

sub : {I : Set} {Γ Δ : List I} {i : I} → ∀ d → (Γ ─Env) (Tm d ∞) Δ →
      Tm d ∞ i Γ → Tm d ∞ i Δ
sub d ρ t = Sem.sem (Substitution d) ρ t
\end{code}
%</substitution>
\begin{code}

-- Simple example: Adding Let-bindings to a language

open import Category.Monad.State as St
open import Category.Applicative
open import Data.String hiding (show ; _==_)
open import Data.Nat.Show

open import Category.Applicative

traverse : ∀ {A} {I : Set} → RawApplicative A →
           {X : List I → I → List I → Set} {i : I} → (d : Desc I) →
           [ ⟦ d ⟧ (λ Δ j Γ → A (X Δ j Γ)) i ⟶ A ∘ ⟦ d ⟧ X i ]
traverse {A} app {X} = go where

  module A = RawApplicative app
  open A

  go : ∀ {i} d → [ ⟦ d ⟧ (λ Δ j Γ → A (X Δ j Γ)) i ⟶ A ∘ ⟦ d ⟧ X i ]
  go (`σ A d)    (a , t)  = (λ b → a , b) A.<$> go (d a) t
  go (`X Δ j d)  (r , t)  = _,_ A.<$> r ⊛ go d t
  go (`∎ i)      t        = pure t


\end{code}
\begin{code}

{- TODO: fix this
Printing : {d : Desc} →
           [ ⟦ d ⟧ (λ _ _ → String) ⟶ const String ] →
           Sem d (λ _ → String) (λ _ → State ℕ String)
Printing {d} printer = record
  { th^𝓥  = λ s _ → s
  ; var    = return
  ; alg    = λ t s → traverse {!!} d (fmap d {!!} t) }
  where open RawMonadState (StateMonadState ℕ)
-}
\end{code}
\begin{code}

\end{code}
%<*letcode>
\begin{code}
Let : {I : Set} → Desc I
Let {I} =  `σ (List I) $ λ Δ →
           `σ I        $ λ i →
           `Xs Δ i i
\end{code}
%</letcode>
%<*unletcode>
\begin{code}
UnLet : (I : Set) (d : Desc I) → Sem (Let `+ d) (Tm d ∞) (Tm d ∞)
Sem.th^𝓥  (UnLet I d) = th^Tm
Sem.var   (UnLet I d) = id
Sem.alg   (UnLet I d) = case alg' (Sem.alg (Substitution d))
\end{code}
%</unletcode>
\begin{code}
  where

  Val : ∀ d → List I → I → List I → Set
  Val d = Kripke (Tm d ∞) (Tm d ∞)

  env : {d : Desc I} (Δ : List I) → [ (λ Γ → All (λ i → Val d [] i Γ) Δ) ⟶ (Δ ─Env) (Val d []) ]
  env []       vs        = ε
  env (σ ∷ Δ)  (v ∷ vs)  = env Δ vs ∙ v

  apply : {d : Desc I} (Δ : List I) {i : I} →
          [ Val d Δ i ⟶ (λ Γ → All (λ i → Val d [] i Γ) Δ) ⟶ Tm d ∞ i ]
  apply []        b vs = b
  apply Δ@(_ ∷ _) b vs = b (base vl^Var) (env Δ vs)

  alg' : {d : Desc I} {i : I} → [ ⟦ Let ⟧ (Val d) i ⟶ Tm d ∞ i ]
  alg' (Δ , i , t) = let (es , b , eq) = unXs Δ t
                     in subst (λ i → Tm _ ∞ i _) (sym eq) (apply Δ b es)

\end{code}
%<*unlet>
\begin{code}
unlet : {I : Set} {d : Desc I} {i : I} → [ Tm (Let `+ d) ∞ i ⟶ Tm d ∞ i ]
unlet = Sem.sem (UnLet _ _) (pack `var)
\end{code}
%</unlet>
\begin{code}


-- Nasty example: Normalisation by Evaluation

\end{code}
%<*domain>
\begin{code}
{-# NO_POSITIVITY_CHECK #-}
data Dm {I : Set} (d : Desc I) : Size → I →  List I → Set where 
  V : {s : Size} {i : I} → [ Var i                              ⟶  Dm d s i      ]
  C : {s : Size} {i : I} → [ ⟦ d ⟧ (Kripke (Dm d s) (Dm d s)) i ⟶  Dm d (↑ s) i  ]
  ⊥ : {s : Size} {i : I} → [                                        Dm d (↑ s) i  ]
\end{code}
%</domain>
\begin{code}
module _ {I : Set} {d : Desc I} where

 th^Dm : {s : Size} {i : I} → Thinnable (Dm d s i)
 th^Dm (V k) ρ = V (th^Var k ρ)
 th^Dm (C t) ρ = C (fmap d (λ Θ i kr → th^Kr Θ th^Dm kr ρ) t)
 th^Dm ⊥     ρ = ⊥

 vl^Dm : {s : Size} → VarLike (Dm d s)
 vl^Dm = record { new = V z ; th^𝓥 = th^Dm }


open import Data.Maybe as Maybe
import Category.Monad as CM
import Level
module M = CM.RawMonad (Maybe.monad {Level.zero})
open M

module _ {I : Set} {d : Desc I} where
\end{code}
%<*nbe-setup>
\begin{code}
 reify^Dm  : {s : Size} {i : I} → [ Dm d s i ⟶ Maybe ∘ Tm d ∞ i ]
 nbe       : Alg d (Dm d ∞) (Dm d ∞) → Sem d (Dm d ∞) (Dm d ∞)

 norm      : Alg d (Dm d ∞) (Dm d ∞) → {i : I} → [ Tm d ∞ i ⟶ Maybe ∘ Tm d ∞ i ]
 norm alg  = reify^Dm ∘ Sem.sem (nbe alg) (base vl^Dm)
\end{code}
%</nbe-setup>
\begin{code}
 reify^Dm (V k) = just (`var k)
 reify^Dm (C v) = `con M.<$> traverse (CM.RawMonad.rawIApplicative Maybe.monad) d
                            (fmap d (λ Θ i → reify^Dm ∘ reify vl^Dm Θ i) v)
 reify^Dm ⊥     = nothing

 nbe alg = record
   { th^𝓥  = th^Dm
   ; var    = id
   ; alg    = alg
   }

`id : LC []
`id = `L (`var z)

\end{code}
%<*nbelc>
\begin{code}
norm^LC : [ LC ⟶ Maybe ∘ LC ]
norm^LC = norm $ case app (C ∘ (false ,_)) where

  app : [ ⟦ `X [] tt (`X [] tt (`∎ tt)) ⟧ (Kripke (Dm LCD ∞) (Dm LCD ∞)) tt ⟶ Dm LCD ∞ tt ]
  app (C (false , f , _)  , t  , _) = f (base vl^Var) (ε ∙ t)  -- redex
  app (f                  , t  , _) = C (true , f , t , refl)  -- stuck application
\end{code}
%</nbelc>
\begin{code}
open import Relation.Binary.PropositionalEquality hiding ([_] ; refl)

example : norm^LC (`A `id (`A `id `id)) ≡ just `id
example = _≡_.refl

module inference where

 infixr 5 _⇒_
 data Type : Set where
   α    : Type
   _⇒_  : Type → Type → Type

 infix 1 _==_
 _==_ : Type → Type → Maybe ⊤
 α     == α       = just tt
 σ ⇒ τ == σ' ⇒ τ' = tt <$ ((σ == σ') ⊗ (τ == τ'))
 _     == _       = nothing

 isArrow : Type → Maybe (Type × Type)
 isArrow (σ ⇒ τ) = just (σ , τ)
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
%</bidirectional>
%<*typemode>
\begin{code}
 Type- : Phase → Set
 Type- Check  = Type → Maybe ⊤
 Type- Infer  = Maybe Type
\end{code}
%</typemode>
%<*typecheck>
\begin{code}
 Typecheck : Sem Lang (λ _ _ → Type) (const ∘ Type-)
 Sem.th^𝓥  Typecheck         = λ σ _ → σ
 Sem.var    Typecheck {Check} = _==_
 Sem.var    Typecheck {Infer} = just
 Sem.alg    Typecheck         =
   case app $ case lam $ case cut ann
\end{code}
%</typecheck>
\begin{code}
  where

   app : {i : Phase} → (Maybe Type) × (Type → Maybe ⊤) × i ≡ Infer → Type- i
   app (just (σ ⇒ τ)  , f , refl) = τ <$ f σ
   app (_             , _ , refl) = nothing

   lam : {i : Phase} {Γ : List Phase} → □ (_ ⟶ κ (Type- Check)) Γ × i ≡ Check → Type- i
   lam (f , refl) (σ ⇒ τ)  = f (base vl^Var) (ε ∙ σ) τ

   lam (_ , refl) _        = nothing

   cut : {i : Phase} → Type × (Type → Maybe ⊤) × i ≡ Infer → Type- i
   cut (σ , f , refl) = σ <$ f σ

   ann : {i : Phase} → Maybe Type × i ≡ Check → Type- i
   ann (just σ  , refl) = σ ==_
   ann (_       , refl) = const nothing

 pattern app f t  = `con (true , f , t , refl)
 pattern lam b    = `con (false , true , b , refl)
 pattern cut σ t  = `con (false , false , true , σ , t , refl)
 pattern emb t    = `con (false , false , false , t , refl)

 type- : (p : Phase) → Tm Lang ∞ p [] → Type- p
 type- p t = Sem.sem Typecheck {Δ = []} ε t

 _ : let  id  : Tm Lang ∞ Check []
          id  = lam (emb (`var z))
     in Is-just $ type- Check (emb (app (cut ((α ⇒ α) ⇒ (α ⇒ α)) id) id)) (α ⇒ α)
 _ = just tt
\end{code}



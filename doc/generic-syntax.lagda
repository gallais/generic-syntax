\begin{code}
module generic-syntax where

open import Level using (Level)
open import Size
open import Data.Bool
open import Data.Nat as ℕ
open import Data.Unit
open import Data.Sum as Sum
open import Data.Product as Prod hiding (,_)
open import Function

open import var
open import indexed 
open import environment hiding (refl)

\end{code}
%<*desc>
\begin{code}
data Desc : Set₁ where
  `σ : (A : Set) (d : A → Desc)  →  Desc
  `X : ℕ   → Desc                →  Desc
  `∎ :                              Desc
\end{code}
%</desc>
\begin{code}

infixr 6 _`×_
infixr 5 _`+_

`K : Set → Desc
`K A = `σ A (λ _ → `∎)


\end{code}
%<*sumcomb>
\begin{code}
_`+_ : Desc → Desc → Desc
d `+ e =  `σ Bool $ λ isLeft →
          if isLeft then d else e
\end{code}
%</sumcomb>
%<*paircomb>
\begin{code}
_`×_ : Desc → Desc → Desc
`σ A d  `× e = `σ A (λ a → d a `× e)
`X k d  `× e = `X k (d `× e)
`∎      `× e = e
\end{code}
%</paircomb>
%<*interp>
\begin{code}
⟦_⟧ : Desc → (ℕ → ℕ → Set) → (ℕ → Set)
⟦ `σ A d  ⟧ X n = Σ[ a ∈ A ] (⟦ d a ⟧ X n)
⟦ `X m d  ⟧ X n = X m n × ⟦ d ⟧ X n
⟦ `∎      ⟧ X n = ⊤
\end{code}
%</interp>
\begin{code}

module _ (d e : Desc) {ρ : ℕ → ℕ → Set} where
\end{code}
%<*pairunpair>
\begin{code}
 pair    : [ ⟦ d ⟧ ρ ⟶ ⟦ e ⟧ ρ ⟶ ⟦ d `× e ⟧ ρ   ]
 unpair  : [ ⟦ d `× e ⟧ ρ ⟶ ⟦ d ⟧ ρ ∙× ⟦ e ⟧ ρ  ]
\end{code}
%</pairunpair>
\begin{code}
 pair = go d where
 
  go : ∀ d → [ ⟦ d ⟧ ρ ⟶ ⟦ e ⟧ ρ ⟶ ⟦ d `× e ⟧ ρ   ]
  go (`σ A d) (a , a')  b = a , go (d a) a' b
  go (`X x d) (r , a')  b = r , go d a' b
  go `∎        a         b = b

 unpair = go d where

  go : ∀ d → [ ⟦ d `× e ⟧ ρ ⟶ ⟦ d ⟧ ρ ∙× ⟦ e ⟧ ρ  ]
  go (`σ A d) (a , ab)  = Prod.map (λ b → a , b) id (go (d a) ab)
  go (`X x d) (r , ab)  = Prod.map (λ b → r , b) id (go d ab)
  go `∎       ab        = tt , ab
\end{code}
%<*case>
\begin{code}
case : {d e : Desc} {ρ : ℕ → ℕ → Set} {A : Set} {n : ℕ} →  (⟦ d       ⟧ ρ n  → A) →
                                                           (⟦ e       ⟧ ρ n  → A) →
                                                           (⟦ d `+ e  ⟧ ρ n  → A)
\end{code}
%</case>
\begin{code}
case l r (true   , t) = l t
case l r (false  , t) = r t

fmap : (d : Desc) {X Y : ℕ → ℕ → Set} {n p : ℕ} → (∀ m → X m n → Y m p) → ⟦ d ⟧ X n → ⟦ d ⟧ Y p
fmap (`σ A d)  f = Prod.map id (fmap (d _) f)
fmap (`X m d)  f = Prod.map (f _) (fmap d f)
fmap `∎        f = id

\end{code}
%<*scope>
\begin{code}
Scope : (ℕ → Set) → (ℕ → ℕ → Set)
Scope T m = (m +_) ⊢ T
\end{code}
%</scope>
%<*mu>
\begin{code}
data Tm (d : Desc) : Size → ℕ → Set where
  `var : {i : Size} →  [ Var                     ⟶ Tm d (↑ i)  ]
  `con : {i : Size} →  [ ⟦ d ⟧ (Scope (Tm d i))  ⟶ Tm d (↑ i)  ]
\end{code}
%</mu>

%<*LCD>
\begin{code}
LCD : Desc
LCD =  `σ Bool $ λ isApp →
       if isApp then `X 0 (`X 0 `∎) else `X 1 `∎
\end{code}
%</LCD>
%<*LC>
\begin{code}
LC : ℕ → Set
LC = Tm LCD ∞
\end{code}
%</LC>
%<*var>
\begin{code}
`V : [ Var ⟶ LC ]
`V = `var
\end{code}
%</var>
%<*app>
\begin{code}
`A : [ LC ⟶ LC ⟶ LC ]
`A f t = `con (true , f , t , tt)
\end{code}
%</app>
%<*lam>
\begin{code}
`L : [ suc ⊢ LC ⟶ LC ]
`L b = `con (false , b , tt)
\end{code}
%</lam>

%<*semantics>
\begin{code}
record Sem (d : Desc) (𝓥 𝓒 : ℕ → Set) : Set where
  field  th^𝓥   : Thinnable 𝓥
         var    : [ 𝓥                   ⟶ 𝓒 ]
         alg    : [ ⟦ d ⟧ (Kripke 𝓥 𝓒)  ⟶ 𝓒 ]
\end{code}
%</semantics>

%<*sembody>
\begin{code}
  sem   : {m n : ℕ} {i : Size} → (m ─Env) 𝓥 n → Tm d i m → 𝓒 n
  body  : {m n : ℕ} {i : Size} → (m ─Env) 𝓥 n → ∀ k → Scope (Tm d i) k m → Kripke 𝓥 𝓒 k n
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
  body ρ 0        t = sem ρ t
  body ρ (suc k)  t = λ ren vs → sem (vs >> th^Env th^𝓥 ρ ren) t
\end{code}
%</body>
%<*varlike>
\begin{code}
record VarLike (𝓥 : ℕ → Set) : Set where
  field  new   : [ suc ⊢ 𝓥 ]
         th^𝓥  : Thinnable 𝓥
\end{code}
%</varlike>
\begin{code}
  refl : ∀ {n} → (n ─Env) 𝓥 n
  refl {zero}  = ε
  refl {suc n} = th^Env th^𝓥 refl extend ∙ new

  freshʳ : (k : ℕ) → ∀ {n} → (n ─Env) 𝓥 (k ℕ.+ n)
  freshʳ k = th^Env th^𝓥 refl (pack (injectʳ k))

  freshˡ : (k : ℕ) → ∀ {n} → (k ─Env) 𝓥 (k ℕ.+ n)
  freshˡ k = th^Env th^𝓥 refl (pack (injectˡ _))
open VarLike public

vl^Var : VarLike Var
vl^Var = record
  { new    = z
  ; th^𝓥  = th^Var
  }
\end{code}
%<*reify>
\begin{code}
reify : {𝓥 𝓒 : ℕ → Set} {n : ℕ} → VarLike 𝓥 → ∀ m → Kripke 𝓥 𝓒 m n → Scope 𝓒 m n
reify vl^𝓥 zero       b = b
reify vl^𝓥 m@(suc _)  b = b (freshʳ vl^Var m) (freshˡ vl^𝓥 m)
\end{code}
%</reify>
\begin{code}

record Syntactic (d : Desc) (𝓥 : ℕ → Set) : Set where
  field
    var    : [ 𝓥 ⟶ Tm d ∞ ]
    vl^𝓥  : VarLike 𝓥

  semantics : Sem d 𝓥 (Tm d ∞)
  semantics = record
    { var   = var
    ; th^𝓥 = th^𝓥 vl^𝓥
    ; alg   = `con ∘ alg' d
    } where

    alg' : ∀ e → [ ⟦ e ⟧ (Kripke 𝓥 (Tm d ∞)) ⟶ ⟦ e ⟧ ((_⊢ Tm d ∞) ∘ ℕ._+_) ]
    alg' e = fmap e (λ m → reify vl^𝓥 m)

sy^Var : ∀ {d} → Syntactic d Var
sy^Var = record
  { var    = `var
  ; vl^𝓥  = vl^Var
  }
\end{code}
%<*renaming>
\begin{code}
Renaming : ∀ d → Sem d Var (Tm d ∞)
Renaming d = record
  { th^𝓥  = λ k ρ → lookup ρ k
  ; var    = `var
  ; alg    = `con ∘ fmap d (reify vl^Var) }

ren :  {m n : ℕ} → ∀ d → (m ─Env) Var n →
       Tm d ∞ m → Tm d ∞ n
ren d = Sem.sem (Renaming d)
\end{code}
%</renaming>
\begin{code}
th^Tm : ∀ {d} → Thinnable (Tm d ∞)
th^Tm t ρ = Sem.sem (Renaming _) ρ t

vl^Tm : ∀ {d} → VarLike (Tm d ∞)
vl^Tm = record
  { new    = `var z
  ; th^𝓥  = th^Tm
  }

sy^Tm : ∀ {d} → Syntactic d (Tm d ∞)
sy^Tm = record
  { var    = id
  ; vl^𝓥  = vl^Tm
  }

\end{code}
%<*substitution>
\begin{code}
Substitution : ∀ d → Sem d (Tm d ∞) (Tm d ∞)
Substitution d = record
  { th^𝓥  = λ t ρ → Sem.sem (Renaming d) ρ t
  ; var    = id
  ; alg    = `con ∘ fmap d (reify vl^Tm) }

sub :  {m n : ℕ} → ∀ d → (m ─Env) (Tm d ∞) n →
       Tm d ∞ m → Tm d ∞ n
sub d = Sem.sem (Substitution d)
\end{code}
%</substitution>
\begin{code}

-- Simple example: Adding Let-bindings to a language

open import Category.Monad.State as St
open import Category.Applicative
open import Data.String hiding (show ; _==_)
open import Data.Nat.Show

open import Category.Applicative

traverse : ∀ {A} → RawApplicative A → {X : ℕ → ℕ → Set} → (d : Desc) →
           [ ⟦ d ⟧ (λ m n → A (X m n)) ⟶ A ∘ ⟦ d ⟧ X ]
traverse {A} app {X} = go where

  module A = RawApplicative app
  open A

  go : ∀ d → [ ⟦ d ⟧ (λ m n → A (X m n)) ⟶ A ∘ ⟦ d ⟧ X ]
  go (`σ A d)  (a , t)  = (λ b → a , b) A.<$> go (d a) t
  go (`X k d)  (r , t)  = _,_ A.<$> r ⊛ go d t
  go `∎        t        = pure tt


\end{code}
\begin{code}
{- TODO: fix
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
%<*ntimes>
\begin{code}
_times_ : {ℓ : Level} {A : Set ℓ} → ℕ → (A → A) → (A → A)
(zero   times f) d = d
(suc n  times f) d = f ((n times f) d)
\end{code}
%</ntimes>
%<*letcode>
\begin{code}
Let : Desc
Let = `σ ℕ (λ n → (n times `X 0) `∎ `× `X n `∎)
\end{code}
%</letcode>
%<*unletcode>
\begin{code}
UnLet : ∀ d → Sem (Let `+ d) (Tm d ∞) (Tm d ∞)
UnLet d = record
  { th^𝓥  = th^Tm
  ; var    = id
  ; alg    = case alg' (Sem.alg (Substitution d)) }
\end{code}
%</unletcode>
\begin{code}
  where

  Val : ∀ d → ℕ → ℕ → Set
  Val d = Kripke (Tm d ∞) (Tm d ∞)

  env : ∀ {d} n → [ ⟦ (n times `X 0) `∎ ⟧ (Val d) ⟶ (n ─Env) (Val d 0) ]
  env zero     vs        = ε
  env (suc n)  (v , vs)  = env n vs ∙ v

  apply : ∀ {d} n → [ Val d n ⟶ ⟦ (n times `X 0) `∎ ⟧ (Val d) ⟶ Tm d ∞ ]
  apply zero     kr vs = kr
  apply (suc n)  kr vs = kr (refl vl^Var) (env (suc n) vs)

  alg' : ∀ {d} → [ ⟦ `σ ℕ (λ n → (n times `X 0) `∎ `× `X n `∎) ⟧ (Val d) ⟶ Tm d ∞ ]
  alg' (n , t)  =  let (es , b , _) = unpair ((n times `X 0) `∎) (`X n `∎) t
                   in apply n b es


\end{code}
%<*unlet>
\begin{code}
unlet : {d : Desc} → [ Tm (Let `+ d) ∞ ⟶ Tm d ∞ ]
unlet = Sem.sem (UnLet _) (pack `var)
\end{code}
%</unlet>
\begin{code}


-- Nasty example: Normalisation by Evaluation

\end{code}
%<*domain>
\begin{code}
{-# NO_POSITIVITY_CHECK #-}
data Dm (d : Desc) : Size → ℕ → Set where 
  V : {i : Size} → [ Var                               ⟶  Dm d i      ]
  C : {i : Size} → [ ⟦ d ⟧ (Kripke (Dm d i) (Dm d i))  ⟶  Dm d (↑ i)  ]
  ⊥ : {i : Size} → [                                      Dm d (↑ i)  ]
\end{code}
%</domain>
\begin{code}
module _ {d : Desc} where

 th^Dm : {i : Size} → Thinnable (Dm d i)
 th^Dm (V k) ρ = V (th^Var k ρ)
 th^Dm (C t) ρ = C (fmap d (λ m kr → th^Kr m th^Dm kr ρ) t)
 th^Dm ⊥     ρ = ⊥

vl^Dm : ∀ {d i} → VarLike (Dm d i)
vl^Dm = record { new = V z ; th^𝓥 = th^Dm }


open import Data.Maybe as Maybe
import Category.Monad as CM
import Level
module M = CM.RawMonad (Maybe.monad {Level.zero})
open M

module _ {d : Desc} where
\end{code}
%<*nbe-setup>
\begin{code}
 reify^Dm  : {i : Size} → [ Dm d i ⟶ Maybe ∘ Tm d ∞ ]
 nbe       : [ ⟦ d ⟧ (Kripke (Dm d ∞) (Dm d ∞)) ⟶ Dm d ∞ ] → Sem d (Dm d ∞) (Dm d ∞)

 norm      : [ ⟦ d ⟧ (Kripke (Dm d ∞) (Dm d ∞)) ⟶ Dm d ∞ ] → [ Tm d ∞ ⟶ Maybe ∘ Tm d ∞ ]
 norm alg  = reify^Dm ∘ Sem.sem (nbe alg) (refl vl^Dm)
\end{code}
%</nbe-setup>
\begin{code}
 reify^Dm (V k) = just (`var k)
 reify^Dm (C v) = `con M.<$> traverse (CM.RawMonad.rawIApplicative Maybe.monad) d
                            (fmap d (λ m → reify^Dm ∘ reify vl^Dm m) v)
 reify^Dm ⊥     = nothing

 nbe alg = record
   { th^𝓥  = th^Dm
   ; var    = id
   ; alg    = alg
   }

`id : LC 0
`id = `L (`var z)

\end{code}
%<*nbelc>
\begin{code}
norm^LC : [ LC ⟶ Maybe ∘ LC ]
norm^LC = norm $ case app (C ∘ (false ,_)) where

  app : [ ⟦ `X 0 (`X 0 `∎) ⟧ (Kripke (Dm LCD ∞) (Dm LCD ∞)) ⟶ Dm LCD ∞ ]
  app (C (false , f , _)  , t  , _) = f (refl vl^Var) (ε ∙ t)  -- redex
  app (f                  , t  , _) = C (true , f , t , _)     -- stuck application
\end{code}
%</nbelc>
\begin{code}
open import Relation.Binary.PropositionalEquality hiding ([_] ; refl)

example : norm^LC (`A `id (`A `id `id)) ≡ just `id
example = _≡_.refl

infixr 5 _⇒_
data Type : Set where
  α    : Type
  _⇒_  : Type → Type → Type

infix 1 _==_
_==_ : Type → Type → Maybe Type
α     == α       = just α
σ ⇒ τ == σ' ⇒ τ' = σ ⇒ τ <$ ((σ == σ') ⊗ (τ == τ'))
_     == _       = nothing

isArrow : Type → Maybe (Type × Type)
isArrow (σ ⇒ τ) = just (σ , τ)
isArrow _       = nothing


Infer : Desc
Infer =  `X 0 (`X 0 `∎)          -- app
     `+  `X 1 `∎                 -- lam
     `+  `σ Type (λ _ → `X 0 `∎) -- ann

app : [ Tm Infer ∞ ⟶ Tm Infer ∞ ⟶ Tm Infer ∞ ]
app f t = `con (true , f , t , _)

lam : [ suc ⊢ Tm Infer ∞ ⟶ Tm Infer ∞ ]
lam b = `con (false , true , b , _)

ann : [ const Type ⟶ Tm Infer ∞ ⟶ Tm Infer ∞ ]
ann σ t = `con (false , false , σ , t , _)

Check : Set
Check = Maybe Type → Maybe Type

infer : Sem Infer (const Type) (const Check)
infer = record
  { th^𝓥  = λ σ _ → σ
  ; var    = λ σ → maybe (σ ==_) (just σ)
  ; alg    = case  checkApp
           $ case  checkLam
                   checkAnn } where


  checkApp : Check × Check × ⊤ → Check
  checkApp (f , t , _) r =
    f nothing  >>= λ σf →
    isArrow σf >>= uncurry λ σ τ →
    t (just σ) M.>> maybe (τ ==_) (just τ) r

  checkLam : [ □ ((1 ─Env) (const Type) ⟶ const Check) ∙× (const ⊤) ⟶ const Check ]
  checkLam (b , _) r =  r          >>= λ στ →
                        isArrow στ >>= uncurry λ σ τ →
                        b (refl vl^Var) (ε ∙ σ) (just τ)
  
  checkAnn : Type × Check × ⊤ → Check
  checkAnn (σ , t , _) r = t (just σ) M.>> maybe (σ ==_) (just σ) r

typeinference : Tm Infer ∞ 0 → Maybe Type
typeinference t = Sem.sem infer {0} {0} ε t nothing

_ : let id = lam (`var z) in
    typeinference (app (ann ((α ⇒ α) ⇒ (α ⇒ α)) id) id) ≡ just (α ⇒ α)
_ = _≡_.refl

\end{code}



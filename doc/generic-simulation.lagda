\begin{code}
module generic-simulation where

open import Size
open import Data.Unit
open import Data.Bool
open import Data.Nat.Base
open import Data.Fin
open import Data.Product hiding (zip ; ,_)
open import Data.Sum
open import Function

open import indexed
open import var
open import environment
open import generic-syntax

open import Relation.Binary.PropositionalEquality using (_≡_ ; sym ; subst ; cong ; cong₂)

module _ {X Y : ℕ → ℕ → Set} where
\end{code}
%<*ziptype>
\begin{code}
 Zip : (P : (m : ℕ) → [ X m ⟶ Y m ⟶ κ Set ]) (d : Desc) → [ ⟦ d ⟧ X ⟶ ⟦ d ⟧ Y ⟶ κ Set ]
 Zip P `∎        x        y         = ⊤
 Zip P (`X k d)  (r , x)  (r' , y)  = P k r r' × Zip P d x y
 Zip P (`σ A d)  (a , x)  (a' , y)  = Σ[ eq ∈ a' ≡ a ] Zip P (d a) x (rew eq y)
   where rew = subst (λ a → ⟦ d a ⟧ _ _)
\end{code}
%</ziptype>
\begin{code}
 zip : {P : ∀ m → [ X m ⟶ Y m ⟶ κ Set ]} {T : ℕ → ℕ → Set} (d : Desc) {n p : ℕ}
       {f : (m : ℕ) → T m n → X m p} {g : (m : ℕ) → T m n → Y m p}
       (FG : (m : ℕ) (t : T m n) → P m (f m t) (g m t)) →
       (t : ⟦ d ⟧ T n) → Zip P d (fmap d f t) (fmap d g t)
 zip (`σ A d)  FG (a , t) = _≡_.refl , zip (d a) FG t
 zip (`X m d)  FG (r , t) = FG m r , zip d FG t
 zip `∎        FG t        = tt

module _ {X : ℕ → ℕ → Set} where

 refl^Zip : {P : ∀ m → [ X m ⟶ X m ⟶ κ Set ]} →
            (refl^P : ∀ m {n} (x : X m n) → P m x x) →
            (d : Desc) {n : ℕ} (t : ⟦ d ⟧ X n) →
            Zip P d t t
 refl^Zip refl^P (`σ A d)  (a , t) = _≡_.refl , refl^Zip refl^P (d a) t
 refl^Zip refl^P (`X m d)  (r , t) = refl^P m r , refl^Zip refl^P d t
 refl^Zip refl^P `∎         t      = tt

 sym^Zip : {P : ∀ m → [ X m ⟶ X m ⟶ κ Set ]} →
           (sym^P : ∀ m {n} {x y : X m n} → P m x y → P m y x) →
           (d : Desc) {n : ℕ} {t u : ⟦ d ⟧ X n} →
           Zip P d t u → Zip P d u t
 sym^Zip sym^P (`σ A d)  (_≡_.refl  , eq) = _≡_.refl , sym^Zip sym^P (d _) eq
 sym^Zip sym^P (`X m d)  (prs       , eq) = sym^P m prs , sym^Zip sym^P d eq
 sym^Zip sym^P `∎         eq               = tt

 trans^Zip : {P : ∀ m → [ X m ⟶ X m ⟶ κ Set ]} →
           (trans^P : ∀ m {n} {x y z : X m n} → P m x y → P m y z → P m x z) →
           (d : Desc) {n : ℕ} {t u v : ⟦ d ⟧ X n} →
           Zip P d t u → Zip P d u v → Zip P d t v
 trans^Zip trans^P (`σ A d)  (_≡_.refl  , t≈u) (_≡_.refl , u≈v) =
   _≡_.refl , trans^Zip trans^P (d _) t≈u u≈v
 trans^Zip trans^P (`X m d)  (prs       , t≈u) (psq      , u≈v) =
   trans^P m prs psq , trans^Zip trans^P d t≈u u≈v
 trans^Zip trans^P `∎         _                 _                = tt

record Rel (T U : ℕ → Set) : Set₁ where
  constructor mkRel
  field rel : {n : ℕ} → T n → U n → Set
open Rel

module _ {T U : ℕ → Set} where

 record ∀[_] (𝓡 : Rel T U)
             {m n : ℕ} (ρ₁ : (m ─Env) T n) (ρ₂ : (m ─Env) U n) : Set where
   constructor pack^R
   field lookup^R : ∀ k → rel 𝓡 (lookup ρ₁ k) (lookup ρ₂ k)
 open ∀[_] public

module _ {T U : ℕ → Set} {𝓡 : Rel T U} {m n : ℕ} where

 _∙^R_ :  {ρ₁ : (m ─Env) T n} {ρ₂ : (m ─Env) U n} → ∀[ 𝓡 ] ρ₁ ρ₂ →
          {v₁ : T n} {v₂ : U n} → rel 𝓡 v₁ v₂ →
          ∀[ 𝓡 ] (ρ₁ ∙ v₁) (ρ₂ ∙ v₂)
 lookup^R (ρ ∙^R v) z      = v
 lookup^R (ρ ∙^R v) (s k)  = lookup^R ρ k

 _>>^R_ :  {p : ℕ}
           {ρ₁  : (m ─Env) T n} {ρ₂  : (m ─Env) U n} → ∀[ 𝓡 ] ρ₁ ρ₂ →
           {ρ₁′ : (p ─Env) T n} {ρ₂′ : (p ─Env) U n} → ∀[ 𝓡 ] ρ₁′ ρ₂′ →
           ∀[ 𝓡 ] (ρ₁ >> ρ₁′) (ρ₂ >> ρ₂′)
 lookup^R (_>>^R_ ρ^R ρ′^R) k with split m k
 ... | inj₁ k₁ = lookup^R ρ^R k₁
 ... | inj₂ k₂ = lookup^R ρ′^R k₂

 _<$>^R_ : {p : ℕ} {f : T n → T p} {g : U n → U p} →
           ({t : T n} {u : U n} → rel 𝓡 t u → rel 𝓡 (f t) (g u)) →
           {ρ₁ : (m ─Env) T n} {ρ₂ : (m ─Env) U n} →
           ∀[ 𝓡 ] ρ₁ ρ₂ → ∀[ 𝓡 ] (f <$> ρ₁) (g <$> ρ₂)
 lookup^R (F <$>^R ρ) k = F (lookup^R ρ k)

module _ {𝓥₁ 𝓥₂ : ℕ → Set} (𝓡^𝓥  : Rel 𝓥₁ 𝓥₂) where

 record VarLike^R (vl₁ : VarLike 𝓥₁) (vl₂ : VarLike 𝓥₂) : Set where
   field  new^R  : {n : ℕ} → rel 𝓡^𝓥 {suc n} (new vl₁) (new vl₂)
          th^R   : {m n : ℕ} (σ : m ⊆ n) {v₁ : 𝓥₁ m} {v₂ : 𝓥₂ m} →
                   rel 𝓡^𝓥 v₁ v₂ → rel 𝓡^𝓥 (th^𝓥 vl₁ v₁ σ) (th^𝓥 vl₂ v₂ σ)

   refl^R : {n : ℕ} → ∀[ 𝓡^𝓥 ] (VarLike.refl vl₁ {n}) (VarLike.refl vl₂)
   refl^R {zero } = pack^R λ ()
   refl^R {suc n} = (th^R extend <$>^R refl^R) ∙^R new^R

   freshˡ^R : (n : ℕ) {k : ℕ} → ∀[ 𝓡^𝓥 ] (freshˡ vl₁ n {k}) (freshˡ vl₂ n)
   freshˡ^R n = th^R _ <$>^R refl^R

   freshʳ^R : (n : ℕ) {k : ℕ} → ∀[ 𝓡^𝓥 ] (freshʳ vl₁ n {k}) (freshʳ vl₂ n)
   freshʳ^R n = th^R _ <$>^R refl^R

module _ {𝓥₁ 𝓥₂ 𝓒₁ 𝓒₂ : ℕ → Set} (𝓡^𝓥  : Rel 𝓥₁ 𝓥₂) (𝓡^𝓒  : Rel 𝓒₁ 𝓒₂) where

 Kripke^R : (m : ℕ) → {n : ℕ} → Kripke 𝓥₁ 𝓒₁ m n → Kripke 𝓥₂ 𝓒₂ m n → Set
 Kripke^R zero       k₁ k₂ = rel 𝓡^𝓒 k₁ k₂
 Kripke^R m@(suc _)  k₁ k₂ =
   {p : ℕ} (σ : _ ⊆ p) {ρ₁ : (m ─Env) 𝓥₁ _} {ρ₂ : (m ─Env) 𝓥₂ _} →
   ∀[ 𝓡^𝓥 ] ρ₁ ρ₂ → rel 𝓡^𝓒 (k₁ σ ρ₁) (k₂ σ ρ₂)


 reify^R : {vl₁ : VarLike 𝓥₁} {vl₂ : VarLike 𝓥₂} (vl^R : VarLike^R 𝓡^𝓥 vl₁ vl₂) →
           ∀ m → {n : ℕ} {k₁ : Kripke 𝓥₁ 𝓒₁ m n} {k₂ : Kripke 𝓥₂ 𝓒₂ m n} →
           Kripke^R m k₁ k₂ → rel 𝓡^𝓒 (reify vl₁ m k₁) (reify vl₂ m k₂)
 reify^R vl^R zero       k^R = k^R
 reify^R vl^R m@(suc _)  k^R = k^R (freshʳ vl^Var m) (VarLike^R.freshˡ^R vl^R m)

 record Simulate (d : Desc) (𝓢₁ : Sem d 𝓥₁ 𝓒₁) (𝓢₂ : Sem d 𝓥₂ 𝓒₂) : Set where
   field

     th^R : {m n : ℕ} (σ : m ⊆ n) {v₁ : 𝓥₁ m} {v₂ : 𝓥₂ m} →
            rel 𝓡^𝓥 v₁ v₂ → rel 𝓡^𝓥 (Sem.th^𝓥 𝓢₁ v₁ σ) (Sem.th^𝓥 𝓢₂ v₂ σ)

     var^R : {m : ℕ} {v₁ : 𝓥₁ m} {v₂ : 𝓥₂ m} →
             rel 𝓡^𝓥 v₁ v₂ → rel 𝓡^𝓒 (Sem.var 𝓢₁ v₁) (Sem.var 𝓢₂ v₂)

     alg^R : {m : ℕ} {b₁ :
\end{code}
%<*algone>
\begin{code}
             ⟦ d ⟧ (Kripke 𝓥₁ 𝓒₁) m
\end{code}
%</algone>
\begin{code}
             } {b₂ :
\end{code}
%<*algtwo>
\begin{code}
             ⟦ d ⟧ (Kripke 𝓥₂ 𝓒₂) m
\end{code}
%</algtwo>
\begin{code}
             } →
             Zip Kripke^R d b₁ b₂ → rel 𝓡^𝓒 (Sem.alg 𝓢₁ b₁) (Sem.alg 𝓢₂ b₂)


   sim : {m n : ℕ} {ρ₁ : (m ─Env) 𝓥₁ n} {ρ₂ : (m ─Env) 𝓥₂ n}  → ∀[ 𝓡^𝓥 ] ρ₁ ρ₂ →
         {i : Size} (t : Tm d i m) → rel 𝓡^𝓒 (Sem.sem 𝓢₁ ρ₁ t) (Sem.sem 𝓢₂ ρ₂ t)

   body : {n p : ℕ} {ρ₁ : (n ─Env) 𝓥₁ p} {ρ₂ : (n ─Env) 𝓥₂ p}  → ∀[ 𝓡^𝓥 ] ρ₁ ρ₂ →
          {i : Size} (m : ℕ) (t : Scope (Tm d i) m n) →
          Kripke^R m (Sem.body 𝓢₁ ρ₁ m t) (Sem.body 𝓢₂ ρ₂ m t)

   sim ρ (`var k) = var^R (lookup^R ρ k)
   sim ρ (`con t) = alg^R (zip d (body ρ) t)
  
   body ρ zero     t = sim ρ t
   body ρ (suc m)  t = λ σ ρ′ → sim (ρ′ >>^R (th^R σ <$>^R ρ)) t

module _ {𝓥₁ 𝓥₂ 𝓒 : ℕ → Set} (𝓡^𝓥 : Rel 𝓥₁ 𝓥₂) where

 zip^reify : {m : ℕ}  {vl^𝓥₁ : VarLike 𝓥₁} {vl^𝓥₂ : VarLike 𝓥₂}
             (eq : (p : ℕ) {t₁ : Kripke 𝓥₁ 𝓒 p m} {t₂ : Kripke 𝓥₂ 𝓒 p m} →
                   Kripke^R 𝓡^𝓥 (mkRel _≡_) p t₁ t₂ →
                   reify vl^𝓥₁ p t₁ ≡ reify vl^𝓥₂ p t₂) →
             (d : Desc) {b₁ : ⟦ d ⟧ (Kripke 𝓥₁ 𝓒) m} {b₂ : ⟦ d ⟧ (Kripke 𝓥₂ 𝓒) m} →
             Zip (Kripke^R 𝓡^𝓥 (mkRel _≡_)) d b₁ b₂ →
             fmap d {X = Kripke 𝓥₁ 𝓒} {Y = Scope 𝓒} (reify vl^𝓥₁) b₁ ≡ fmap d (reify vl^𝓥₂) b₂
 zip^reify eq (`σ A d)  (_≡_.refl , zp)  = cong (_ ,_) (zip^reify eq (d _) zp)
 zip^reify eq (`X m d)  (r , zp)         = cong₂ _,_ (eq m r) (zip^reify eq d zp)
 zip^reify eq `∎         zp               = _≡_.refl


VarTm^R : (d : Desc) → Rel Var (Tm d ∞)
VarTm^R d = mkRel (_≡_ ∘ `var)

Eq^R : {A : ℕ → Set} → Rel A A
Eq^R = mkRel _≡_

vl^VarTm : (d : Desc) → VarLike^R (VarTm^R d) vl^Var vl^Tm 
vl^VarTm d = record
  { new^R  = _≡_.refl
  ; th^R   = λ σ → cong (Sem.sem (Renaming d) σ) }


RenSub : (d : Desc) → Simulate (VarTm^R d) Eq^R d (Renaming d) (Substitution d)
RenSub d = record
  { var^R = id
  ; th^R  = λ { _ _≡_.refl → _≡_.refl }
  ; alg^R = cong `con ∘ zip^reify (mkRel (_≡_ ∘ `var))
            (λ p → reify^R (VarTm^R d) Eq^R (vl^VarTm d) p) d }

\end{code}
%<*rensub>
\begin{code}
rensub :  (d : Desc) {m n : ℕ} (ρ : m ⊆ n) (t : Tm d ∞ m) →
          Sem.sem (Renaming d) ρ t ≡ Sem.sem (Substitution d) (`var <$> ρ) t
rensub d ρ = Simulate.sim (RenSub d) (pack^R (λ _ → _≡_.refl))
\end{code}
%</rensub>

\begin{code}
module generic-simulation where

open import Size
open import Data.Unit
open import Data.Bool
open import Data.Nat.Base
open import Data.List hiding ([_] ; zip)
open import Data.Product hiding (zip ; ,_)
open import Data.Sum
open import Function

open import indexed
open import var hiding (_<$>_)
open import environment hiding (refl)
open import generic-syntax

open import Relation.Binary.PropositionalEquality hiding ([_])

module _ {I : Set} {X Y : List I → I → List I → Set} where
\end{code}
%<*ziptype>
\begin{code}
 Zip :  (d : Desc I) (R : (δ : List I) (i : I) → [ X δ i ⟶ Y δ i ⟶ κ Set ]) →
        {i : I} → [ ⟦ d ⟧ X i ⟶ ⟦ d ⟧ Y i ⟶ κ Set ]
 Zip (`∎ i′)     R x        y         = ⊤
 Zip (`X δ j d)  R (r , x)  (r' , y)  = R δ j r r' × Zip d R x y
 Zip (`σ A d)    R (a , x)  (a' , y)  = Σ[ eq ∈ a' ≡ a ] Zip (d a) R x (rew eq y)
   where rew = subst (λ a → ⟦ d a ⟧ _ _ _)
\end{code}
%</ziptype>
\begin{code}
module _ {I : Set} {X Y T : List I → I → List I → Set} 
         {P : ∀ δ i → [ X δ i ⟶ Y δ i ⟶ κ Set ]} where
 zip : (d : Desc I) {γ γ′ : List I}
       {f : ∀ δ i → T δ i γ → X δ i γ′} {g : ∀ δ i → T δ i γ → Y δ i γ′}
       (FG : ∀ δ i → (t : T δ i γ) → P δ i (f δ i t) (g δ i t)) →
       {i : I} (t : ⟦ d ⟧ T i γ) → Zip d P (fmap d f t) (fmap d g t)
 zip (`σ A d)    FG (a , t)  = refl , zip (d a) FG t
 zip (`X δ i d)  FG (r , t)  = FG δ i r , zip d FG t
 zip (`∎ i′)     FG t        = tt

module _ {I : Set} {X : List I → I → List I → Set}
         {P : ∀ δ i → [ X δ i ⟶ X δ i ⟶ κ Set ]} where

 refl^Zip :  (refl^P : ∀ δ i {γ} (x : X δ i γ) → P δ i x x) →
             (d : Desc I) {i : I} {γ : List I} (t : ⟦ d ⟧ X i γ) →
             Zip d P t t
 refl^Zip refl^P (`σ A d)    (a , t)  = refl , refl^Zip refl^P (d a) t
 refl^Zip refl^P (`X δ i d)  (r , t)  = refl^P δ i r , refl^Zip refl^P d t
 refl^Zip refl^P (`∎ i′)      t       = tt

 sym^Zip :  (sym^P : ∀ δ i {γ} {x y : X δ i γ} → P δ i x y → P δ i y x) →
            (d : Desc I) {i : I} {γ : List I} {t u : ⟦ d ⟧ X i γ} →
            Zip d P t u → Zip d P u t
 sym^Zip sym^P (`σ A d)    (refl  , eq)  = refl , sym^Zip sym^P (d _) eq
 sym^Zip sym^P (`X δ i d)  (prs       , eq)  = sym^P δ i prs , sym^Zip sym^P d eq
 sym^Zip sym^P (`∎ i′)      eq                = tt

 trans^Zip :  (trans^P : ∀ δ i {γ} {x y z : X δ i γ} → P δ i x y  → P δ i y z → P δ i x z)
              (d : Desc I) {i : I} {γ : List I} {t u v : ⟦ d ⟧ X i γ} →
              Zip d P t u → Zip d P u v → Zip d P t v
 trans^Zip trans^P (`σ A d)  (refl  , t≈u) (refl , u≈v) =
   refl , trans^Zip trans^P (d _) t≈u u≈v
 trans^Zip trans^P (`X δ i d)  (prs       , t≈u) (psq      , u≈v) =
   trans^P δ i prs psq , trans^Zip trans^P d t≈u u≈v
 trans^Zip trans^P (`∎ i′)         _                 _             = tt

record Rel {I : Set} (T U : I → List I → Set) : Set₁ where
  constructor mkRel
  field rel : {i : I} → [ T i ⟶ U i ⟶ κ Set ]
open Rel

module _ {I : Set} {T U : I → List I → Set} where

 record ∀[_] (𝓡 : Rel T U) {Γ Δ : List I}
             (ρ₁ : (Γ ─Env) T Δ) (ρ₂ : (Γ ─Env) U Δ) : Set where
   constructor pack^R
   field lookup^R : ∀ {i} k → rel 𝓡 {i} (lookup ρ₁ k) (lookup ρ₂ k)
 open ∀[_] public

module _ {I : Set} {T U : I → List I → Set} 
         {𝓡 : Rel T U} {Γ Δ : List I} where

 _∙^R_ :  {ρ₁ : (Γ ─Env) T Δ} {ρ₂ : (Γ ─Env) U Δ} → ∀[ 𝓡 ] ρ₁ ρ₂ →
          {i : I} {v₁ : T i Δ} {v₂ : U i Δ} → rel 𝓡 v₁ v₂ →
          ∀[ 𝓡 ] (ρ₁ ∙ v₁) (ρ₂ ∙ v₂)
 lookup^R (ρ ∙^R v) z      = v
 lookup^R (ρ ∙^R v) (s k)  = lookup^R ρ k

 _>>^R_ :  {Γ′ : List I}
           {ρ₁  : (Γ  ─Env) T Δ} {ρ₂  : (Γ  ─Env) U Δ} → ∀[ 𝓡 ] ρ₁ ρ₂ →
           {ρ₁′ : (Γ′ ─Env) T Δ} {ρ₂′ : (Γ′ ─Env) U Δ} → ∀[ 𝓡 ] ρ₁′ ρ₂′ →
           ∀[ 𝓡 ] (ρ₁ >> ρ₁′) (ρ₂ >> ρ₂′)
 lookup^R (_>>^R_ ρ^R ρ′^R) k with split Γ k
 ... | inj₁ k₁ = lookup^R ρ^R k₁
 ... | inj₂ k₂ = lookup^R ρ′^R k₂

 _<$>^R_ : {Θ : List I} {f : {i : I} → T i Δ → T i Θ} {g : {i : I} → U i Δ → U i Θ} →
           ({i : I} {t : T i Δ} {u : U i Δ} → rel 𝓡 t u → rel 𝓡 (f t) (g u)) →
           {ρ₁ : (Γ ─Env) T Δ} {ρ₂ : (Γ ─Env) U Δ} →
           ∀[ 𝓡 ] ρ₁ ρ₂ → ∀[ 𝓡 ] (f <$> ρ₁) (g <$> ρ₂)
 lookup^R (F <$>^R ρ) k = F (lookup^R ρ k)

module _ {I : Set} {𝓥₁ 𝓥₂ : I → List I → Set} (𝓡^𝓥  : Rel 𝓥₁ 𝓥₂) where

 record VarLike^R (vl₁ : VarLike 𝓥₁) (vl₂ : VarLike 𝓥₂) : Set where
   field  new^R  : {i : I} {Γ : List I} → rel 𝓡^𝓥 {i} {i ∷ Γ} (new vl₁) (new vl₂)
          th^R   : {i : I} {Γ Δ : List I} (σ : Thinning Γ Δ) {v₁ : 𝓥₁ i Γ} {v₂ : 𝓥₂ i Γ} →
                   rel 𝓡^𝓥 v₁ v₂ → rel 𝓡^𝓥 (th^𝓥 vl₁ v₁ σ) (th^𝓥 vl₂ v₂ σ)

   base^R : {Γ : List I} → ∀[ 𝓡^𝓥 ] (base vl₁ {Γ}) (base vl₂)
   base^R {[]   } = pack^R λ ()
   base^R {i ∷ Γ} = (th^R extend <$>^R base^R) ∙^R new^R

   freshˡ^R : (Γ : List I) {Δ : List I} → ∀[ 𝓡^𝓥 ] (freshˡ vl₁ Γ {Δ}) (freshˡ vl₂ Γ)
   freshˡ^R n = th^R _ <$>^R base^R

   freshʳ^R : (Γ : List I) {Δ : List I} → ∀[ 𝓡^𝓥 ] (freshʳ vl₁ Γ {Δ}) (freshʳ vl₂ Γ)
   freshʳ^R n = th^R _ <$>^R base^R

module _ {I : Set} {𝓥₁ 𝓥₂ 𝓒₁ 𝓒₂ : I → List I → Set} (𝓡^𝓥  : Rel 𝓥₁ 𝓥₂) (𝓡^𝓒  : Rel 𝓒₁ 𝓒₂) where

\end{code}
%<*kripkeR>
\begin{code}
 Kripke^R : (Δ : List I) (τ : I) → [ Kripke 𝓥₁ 𝓒₁ Δ τ ⟶ Kripke 𝓥₂ 𝓒₂ Δ τ ⟶ κ Set ]
 Kripke^R []       σ k₁ k₂ = rel 𝓡^𝓒 k₁ k₂
 Kripke^R (τ ∷ Δ)  σ k₁ k₂ = {Θ : List I} → ∀ th {ρ₁} {ρ₂} → ∀[ 𝓡^𝓥 ] ρ₁ ρ₂ → rel 𝓡^𝓒 {σ} {Θ} (k₁ th ρ₁) (k₂ th ρ₂)
\end{code}
%</kripkeR>

\begin{code}
 reify^R : {vl₁ : VarLike 𝓥₁} {vl₂ : VarLike 𝓥₂} (vl^R : VarLike^R 𝓡^𝓥 vl₁ vl₂) →
           {Γ : List I} → ∀ Δ σ → {k₁ : Kripke 𝓥₁ 𝓒₁ Δ σ Γ} {k₂ : Kripke 𝓥₂ 𝓒₂ Δ σ Γ} →
           Kripke^R Δ σ k₁ k₂ → rel 𝓡^𝓒 (reify vl₁ Δ σ k₁) (reify vl₂ Δ σ k₂)
 reify^R vl^R []         σ k^R = k^R
 reify^R vl^R Δ@(_ ∷ _)  σ k^R = k^R (freshʳ vl^Var Δ) (VarLike^R.freshˡ^R vl^R _)
\end{code}

%<*recsim>
\begin{code}
 record Sim (d : Desc I) (𝓢₁ : Sem d 𝓥₁ 𝓒₁) (𝓢₂ : Sem d 𝓥₂ 𝓒₂) : Set where
   field  th^R   : {Γ Δ : List I} {i : I} {v₁ : 𝓥₁ i Γ} {v₂ : 𝓥₂ i Γ} → (σ : Thinning Γ Δ) → rel 𝓡^𝓥 v₁ v₂ → rel 𝓡^𝓥 (Sem.th^𝓥 𝓢₁ v₁ σ) (Sem.th^𝓥 𝓢₂ v₂ σ)
          var^R  : {Γ : List I} {i : I} {v₁ : 𝓥₁ i Γ} {v₂ : 𝓥₂ i Γ} → rel 𝓡^𝓥 v₁ v₂ → rel 𝓡^𝓒 (Sem.var 𝓢₁ v₁) (Sem.var 𝓢₂ v₂)
          alg^R  : {Γ : List I} {i : I} {b₁ : ⟦ d ⟧ (Kripke 𝓥₁ 𝓒₁) i Γ} {b₂ : ⟦ d ⟧ (Kripke 𝓥₂ 𝓒₂) i Γ} → Zip d Kripke^R b₁ b₂ → rel 𝓡^𝓒 (Sem.alg 𝓢₁ b₁) (Sem.alg 𝓢₂ b₂)
\end{code}
%</recsim>
%<*simbody>
\begin{code}
   sim   :  {Γ Δ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Γ ─Env) 𝓥₂ Δ} {i : I} {s : Size} → ∀[ 𝓡^𝓥 ] ρ₁ ρ₂ → (t : Tm d s i Γ) → rel 𝓡^𝓒 (Sem.sem 𝓢₁ ρ₁ t) (Sem.sem 𝓢₂ ρ₂ t)
   body  :  {Δ Θ : List I} {ρ₁ : (Δ ─Env) 𝓥₁ Θ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {s : Size} → ∀[ 𝓡^𝓥 ] ρ₁ ρ₂ → (Γ : List I) (i : I) (t : Scope (Tm d s) Γ i Δ) →
            Kripke^R Γ i (Sem.body 𝓢₁ ρ₁ Γ i t) (Sem.body 𝓢₂ ρ₂ Γ i t)
\end{code}
%</simbody>
\begin{code}
   sim ρ (`var k) = var^R (lookup^R ρ k)
   sim ρ (`con t) = alg^R (zip d (body ρ) t)
  
   body ρ []       i t = sim ρ t
   body ρ (σ ∷ Δ)  i t = λ σ ρ′ → sim (ρ′ >>^R (th^R σ <$>^R ρ)) t

module _ {I : Set} {𝓥₁ 𝓥₂ 𝓒 : I → List I → Set} (𝓡^𝓥  : Rel 𝓥₁ 𝓥₂) where

 zip^reify : {Γ : List I}  {vl^𝓥₁ : VarLike 𝓥₁} {vl^𝓥₂ : VarLike 𝓥₂}
             (eq : (Δ : List I) (σ : I) {t₁ : Kripke 𝓥₁ 𝓒 Δ σ Γ} {t₂ : Kripke 𝓥₂ 𝓒 Δ σ Γ} →
                   Kripke^R 𝓡^𝓥 (mkRel _≡_) Δ σ t₁ t₂ →
                   reify vl^𝓥₁ Δ σ t₁ ≡ reify vl^𝓥₂ Δ σ t₂) →
             (d : Desc I) {σ : I} {b₁ : ⟦ d ⟧ (Kripke 𝓥₁ 𝓒) σ Γ} {b₂ : ⟦ d ⟧ (Kripke 𝓥₂ 𝓒) σ Γ} →
             Zip d (Kripke^R 𝓡^𝓥 (mkRel _≡_)) b₁ b₂ →
             fmap d {X = Kripke 𝓥₁ 𝓒} {Y = Scope 𝓒} (reify vl^𝓥₁) b₁ ≡ fmap d (reify vl^𝓥₂) b₂
 zip^reify eq (`σ A d)    (refl , zp)  = cong (_ ,_) (zip^reify eq (d _) zp)
 zip^reify eq (`X δ i d)  (r , zp)         = cong₂ _,_ (eq δ i r) (zip^reify eq d zp)
 zip^reify eq (`∎ i′)      zp               = uip _ _ where
   uip : ∀ {A : Set} {a b : A} (p q : a ≡ b) → p ≡ q
   uip refl refl = refl

module _ {I : Set} where

 VarTm^R : (d : Desc I) → Rel Var (Tm d ∞)
 VarTm^R d = mkRel (_≡_ ∘ `var)

 Eq^R : {A : I → List I → Set} → Rel A A
 Eq^R = mkRel _≡_

 vl^VarTm : (d : Desc I) → VarLike^R (VarTm^R d) vl^Var vl^Tm 
 vl^VarTm d = record
   { new^R  = refl
   ; th^R   = λ σ → cong (Sem.sem (Renaming d) σ) }


 RenSub : (d : Desc I) → Sim (VarTm^R d) Eq^R d (Renaming d) (Substitution d)
 RenSub d = record
   { var^R = id
   ; th^R  = λ { _ refl → refl }
   ; alg^R = cong `con ∘ zip^reify (mkRel (_≡_ ∘ `var))
             (reify^R (VarTm^R d) Eq^R (vl^VarTm d)) d }
\end{code}
%<*rensub>
\begin{code}
 rensub :  {Γ Δ : List I} (d : Desc I) (ρ : Thinning Γ Δ) {i : I} (t : Tm d ∞ i Γ) →
           Sem.sem (Renaming d) ρ t ≡ Sem.sem (Substitution d) (`var <$> ρ) t
 rensub d ρ = Sim.sim (RenSub d) (pack^R (λ _ → refl))
\end{code}
%</rensub>

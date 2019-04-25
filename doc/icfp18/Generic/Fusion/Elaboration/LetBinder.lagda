\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Fusion.Elaboration.LetBinder where

open import Size
open import Data.Bool
open import Data.Product
open import Data.List hiding (lookup)
open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Data.Var hiding (_<$>_)
open import Data.Var.Varlike
open import Data.Relation
open import Data.Environment

open import Generic.Syntax
open import Generic.Syntax.LetBinder
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Semantics.Elaboration.LetBinder
open import Generic.Relator as Relator
open import Generic.Simulation as Simulation
open import Generic.Simulation.Syntactic
open import Generic.Identity
open import Generic.Fusion
open import Generic.Fusion.Utils
open import Generic.Fusion.Syntactic as F
import Generic.Fusion.Specialised.Propositional as FusProp

module _ {I : Set} {d : Desc I} where

 proj₂-eq : ∀ {a b} {A : Set a} {B : A → Set b} {x : A} {b₁ b₂ : B x} →
            (Σ A B ∋ x , b₁) ≡ (x , b₂) → b₁ ≡ b₂
 proj₂-eq refl = refl

 RenUnLet : Fusion (d `+ Let) Ren UnLet UnLet
            (λ Γ Δ ρ₁ ρ₂ → All Eqᴿ Γ (select ρ₁ ρ₂)) Eqᴿ Eqᴿ
 RenUnLet = FusProp.ren-sem (d `+ Let) UnLet $ λ where
   (false , `IN' e t) ρᴿ (refl , refl , eq^e , eq^t , _) → eq^t (pack id) (εᴿ ∙ᴿ eq^e)
   (true , t)         ρᴿ zp → cong `con $ proj₂-eq $
     Relator.reifyᴿ Eqᴿ (d `+ Let) (Simulation.reifyᴿ Eqᴿ Eqᴿ (vl^Refl vl^Tm)) zp

 unLetRen : ∀ {Γ Δ Θ σ s} (t : Tm (d `+ Let) s σ Γ) {ρ₁ ρ₃} {ρ₂ : Thinning Δ Θ} →
            All Eqᴿ _ (ren ρ₂ <$> ρ₁) ρ₃ → ren ρ₂ (unLet ρ₁ t) ≡ unLet ρ₃ t
 unLetRen-body :
   ∀ Ξ σ {Γ Δ Θ s} (t : Scope (Tm (d `+ Let) s) Ξ σ Γ) {ρ₁ ρ₃} {ρ₂ : Thinning Δ Θ} →
   All Eqᴿ _ (ren ρ₂ <$> ρ₁) ρ₃ →
   reify vl^Var Ξ σ (Semantics.body Ren ρ₂ Ξ σ (reify vl^Tm Ξ σ (Semantics.body UnLet ρ₁ Ξ σ t)))
   ≡ reify vl^Tm Ξ σ (Semantics.body UnLet ρ₃ Ξ σ t)

 unLetRen (`var v) ρᴿ = lookupᴿ ρᴿ v
 unLetRen (`con (false , (σ , τ) , e , t , refl)) {ρ₁} {ρ₃} {ρ₂} ρᴿ = unLetRen t $ packᴿ $ λ where
   z     → unLetRen e ρᴿ
   (s v) → begin
     ren ρ₂ (ren (pack id) (lookup ρ₁ v))
       ≡⟨ cong (ren ρ₂) (ren-id′ (lookup ρ₁ v)) ⟩
     ren ρ₂ (lookup ρ₁ v)
       ≡⟨ lookupᴿ ρᴿ v ⟩
     lookup ρ₃ v
       ≡⟨ sym (ren-id′ (lookup ρ₃ v)) ⟩
     ren (pack id) (lookup ρ₃ v)
       ∎
 unLetRen (`con (true  , r)) {ρ₁} {ρ₃} {ρ₂} ρᴿ = cong `con $ begin
   fmap d (reify vl^Var) (fmap d (Semantics.body Ren ρ₂) (fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₁) r)))
     ≡⟨ fmap² d (Semantics.body Ren ρ₂) (reify vl^Var) (fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₁) r)) ⟩
   fmap d _ (fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₁) r))
     ≡⟨ fmap² d (reify vl^Tm) _ _ ⟩
   fmap d _ (fmap d (Semantics.body UnLet ρ₁) r)
     ≡⟨ fmap² d (Semantics.body UnLet ρ₁) _ _ ⟩
   fmap d _ r
     ≡⟨ fmap-ext d (λ Ξ i b → unLetRen-body Ξ i b ρᴿ) r ⟩
   fmap d (λ Φ i → reify vl^Tm Φ i ∘ Semantics.body UnLet ρ₃ Φ i) r
     ≡⟨ sym (fmap² d (Semantics.body UnLet ρ₃) (reify vl^Tm) r) ⟩
   fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₃) r)
     ∎

 unLetRen-body [] σ t ρᴿ = unLetRen t ρᴿ
 unLetRen-body Ξ@(x ∷ xs) σ {Γ} {Δ} {Θ} t {ρ₁} {ρ₃} {ρ₂} ρᴿ = unLetRen t ρ′ᴿ where

  ρ₁₁ : Thinning Ξ (Ξ ++ Θ)
  ρ₁₁ = th^Env th^Var (base vl^Var) (pack (injectˡ Θ))
  ρ₁₂ = th^Env th^Var ρ₂ (th^Env th^Var (base vl^Var) (pack (injectʳ Ξ)))

  ρ₁₃ = pack (injectˡ Θ {Ξ}) >> th^Env th^Var ρ₂ (pack (injectʳ Ξ))

  eq₁₁ᴿ : All Eqᴿ _ ρ₁₁ (pack (injectˡ Θ))
  lookupᴿ eq₁₁ᴿ k = cong (injectˡ Θ) (lookup-base^Var k)

  eq₁₂ᴿ : All Eqᴿ _ ρ₁₂ (th^Env th^Var ρ₂ (pack (injectʳ Ξ)))
  lookupᴿ eq₁₂ᴿ k = cong (injectʳ Ξ) (lookup-base^Var (lookup ρ₂ k))

  eq₁ᴿ : All Eqᴿ _ (ρ₁₁ >> ρ₁₂) ρ₁₃
  eq₁ᴿ = eq₁₁ᴿ >>ᴿ eq₁₂ᴿ


  ρ′ᴿ : All Eqᴿ _ (ren (freshˡ vl^Var Θ >> th^Env th^Var ρ₂ (freshʳ vl^Var Ξ))
                    <$> (freshˡ vl^Tm Δ >> th^Env th^Tm  ρ₁ (freshʳ vl^Var Ξ)))
                  (freshˡ vl^Tm Θ >> th^Env th^Tm ρ₃ (freshʳ vl^Var Ξ))
  lookupᴿ ρ′ᴿ k with split Ξ k
  ... | inj₁ kˡ = begin
    ren (ρ₁₁ >> ρ₁₂) (ren (pack (injectˡ Δ)) (lookup (base vl^Tm) kˡ))
      ≡⟨ cong (ren (ρ₁₁ >> ρ₁₂) ∘ ren (pack (injectˡ Δ))) (lookup-base^Tm kˡ) ⟩
    `var (lookup (ρ₁₁ >> ρ₁₂) (injectˡ Δ kˡ))
      ≡⟨ cong `var (injectˡ->> ρ₁₁ ρ₁₂ kˡ) ⟩
    `var (lookup ρ₁₁ kˡ)
      ≡⟨ cong `var (lookupᴿ eq₁₁ᴿ kˡ) ⟩
    `var (injectˡ Θ kˡ)
      ≡⟨ cong (ren (pack (injectˡ Θ))) (sym (lookup-base^Tm kˡ)) ⟩
    ren (pack (injectˡ Θ)) (lookup (base vl^Tm) kˡ)
      ∎
  ... | inj₂ kʳ = begin
    ren (ρ₁₁ >> ρ₁₂) (ren ρ₂₁ (lookup ρ₁ kʳ))
      ≡⟨ Simulation.sim RenExt eq₁ᴿ (ren ρ₂₁ (lookup ρ₁ kʳ)) ⟩
    ren ρ₁₃ (ren ρ₂₁ (lookup ρ₁ kʳ))
      ≡⟨ cong (ren ρ₁₃) (Simulation.sim RenExt eq₂ᴿ  (lookup ρ₁ kʳ)) ⟩
    ren ρ₁₃ (ren (pack (injectʳ Ξ)) (lookup ρ₁ kʳ))
      ≡⟨ Fusion.fusion (Ren² d) eqᴿ (lookup ρ₁ kʳ) ⟩
    ren (select ρ₂ (pack (injectʳ Ξ))) (lookup ρ₁ kʳ)
      ≡⟨ sym (Fusion.fusion (Ren² d) eq₃ᴿ (lookup ρ₁ kʳ)) ⟩
    ren ρ₃₁ (ren ρ₂ (lookup ρ₁ kʳ))
      ≡⟨ cong (ren ρ₃₁) (lookupᴿ ρᴿ kʳ) ⟩
    ren ρ₃₁ (lookup ρ₃ kʳ)
      ∎ where

    ρ₂₁ = th^Env th^Var (base vl^Var) (pack (injectʳ Ξ))

    eq₂ᴿ : All Eqᴿ _ ρ₂₁ (pack (injectʳ Ξ))
    lookupᴿ eq₂ᴿ k = cong (injectʳ Ξ) (lookup-base^Var k)

    ρ₃₁ = th^Env th^Var (base vl^Var) (pack (injectʳ Ξ))

    eq₃ᴿ : All Eqᴿ _ (select ρ₂ ρ₃₁) (select ρ₂ (pack (injectʳ Ξ)))
    lookupᴿ eq₃ᴿ k = cong (injectʳ Ξ) (lookup-base^Var (lookup ρ₂ k))

    eqᴿ : All Eqᴿ _ (select (pack (injectʳ Ξ)) ρ₁₃) (select ρ₂ (pack (injectʳ Ξ)))
    lookupᴿ eqᴿ k with split Ξ (injectʳ Ξ k) | split-injectʳ Ξ k
    lookupᴿ eqᴿ k | .(inj₂ k) | refl = refl

 SubUnLet : Fusion (d `+ Let) Sub UnLet UnLet
            (λ Γ Δ ρ₁ ρ₂ → All Eqᴿ Γ (unLet ρ₂ <$> ρ₁)) Eqᴿ Eqᴿ
 Fusion.reifyᴬ SubUnLet = λ σ t → t
 Fusion.vl^𝓥ᴬ SubUnLet = vl^Tm
 Fusion.th^𝓔ᴿ   SubUnLet {ρᴬ = ρ₁} {ρᴮ = ρ₂} {ρᴬᴮ = ρ₃} = λ ρᴿ σ → packᴿ λ v → begin
   Semantics.semantics UnLet (th^Env th^Tm ρ₂ σ) (lookup ρ₁ v)
     ≡⟨ sym (unLetRen (lookup ρ₁ v) (packᴿ λ v → refl)) ⟩
   ren σ (unLet ρ₂ (lookup ρ₁ v))
     ≡⟨ cong (ren σ) (lookupᴿ ρᴿ v) ⟩
   ren σ (lookup ρ₃ v)
    ∎
 Fusion._>>ᴿ_   SubUnLet {ρᴬ = ρ₁} = subBodyEnv UnLet RenUnLet (λ σ t → refl) ρ₁
 Fusion.varᴿ  SubUnLet = λ ρᴿ → lookupᴿ ρᴿ
 Fusion.algᴿ  SubUnLet ρᴿ (false , `IN' e t) (refl , refl , eq^e , eq^t , _)
   = eq^t (pack id) (εᴿ ∙ᴿ eq^e)
 Fusion.algᴿ  SubUnLet {ρᴬ = ρ₁} {ρᴮ = ρ₂} {ρᴬᴮ = ρ₃} ρᴿ (true , t) eq^t
   = cong `con $ begin
     let t′ = fmap d (Semantics.body Sub ρ₁) t in
     fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₂) (fmap d (reify vl^Tm) t′))
       ≡⟨ cong (fmap d (reify vl^Tm)) (fmap² d (reify vl^Tm) (Semantics.body UnLet ρ₂) t′) ⟩
     fmap d (reify vl^Tm) (fmap d (λ Δ i → Semantics.body UnLet ρ₂ Δ i ∘ reify vl^Tm Δ i) t′)
       ≡⟨ proj₂-eq $ Relator.reifyᴿ Eqᴿ (d `+ Let) (Simulation.reifyᴿ Eqᴿ Eqᴿ (vl^Refl vl^Tm)) eq^t ⟩
     fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₃) t)
       ∎

 unLetSub : ∀ {Γ Δ Θ σ s} (t : Tm (d `+ Let) s σ Γ) {ρ₁ ρ₃} {ρ₂ : (Δ ─Env) (Tm d ∞) Θ} →
            All Eqᴿ _ (sub ρ₂ <$> ρ₁) ρ₃ → sub ρ₂ (unLet ρ₁ t) ≡ unLet ρ₃ t
 unLetSub-body :
   ∀ Ξ σ {Γ Δ Θ s} (t : Scope (Tm (d `+ Let) s) Ξ σ Γ) {ρ₁ ρ₃} {ρ₂ : (Δ ─Env) (Tm d ∞) Θ} →
   All Eqᴿ _ (sub ρ₂ <$> ρ₁) ρ₃ →
   reify vl^Tm Ξ σ (Semantics.body Sub ρ₂ Ξ σ (reify vl^Tm Ξ σ (Semantics.body UnLet ρ₁ Ξ σ t)))
   ≡ reify vl^Tm Ξ σ (Semantics.body UnLet ρ₃ Ξ σ t)

 unLetSub (`var v) ρᴿ = lookupᴿ ρᴿ v
 unLetSub (`con (false , (σ , τ) , e , t , refl)) {ρ₁} {ρ₃} {ρ₂} ρᴿ = unLetSub t $ packᴿ $ λ where
   z     → unLetSub e ρᴿ
   (s v) → begin
     sub ρ₂ (ren (pack id) (lookup ρ₁ v))
       ≡⟨ cong (sub ρ₂) (ren-id′ (lookup ρ₁ v)) ⟩
     sub ρ₂ (lookup ρ₁ v)
       ≡⟨ lookupᴿ ρᴿ v ⟩
     lookup ρ₃ v
       ≡⟨ sym (ren-id′ (lookup ρ₃ v)) ⟩
     ren (pack id) (lookup ρ₃ v)
       ∎
 unLetSub (`con (true  , r)) {ρ₁} {ρ₃} {ρ₂} ρᴿ = cong `con $ begin
   fmap d (reify vl^Tm) (fmap d (Semantics.body Sub ρ₂) (fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₁) r)))
     ≡⟨ fmap² d (Semantics.body Sub ρ₂) (reify vl^Tm) (fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₁) r)) ⟩
   fmap d _ (fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₁) r))
     ≡⟨ fmap² d (reify vl^Tm) _ _ ⟩
   fmap d _ (fmap d (Semantics.body UnLet ρ₁) r)
     ≡⟨ fmap² d (Semantics.body UnLet ρ₁) _ _ ⟩
   fmap d _ r
     ≡⟨ fmap-ext d (λ Ξ i b → unLetSub-body Ξ i b ρᴿ) r ⟩
   fmap d (λ Φ i → reify vl^Tm Φ i ∘ Semantics.body UnLet ρ₃ Φ i) r
     ≡⟨ sym (fmap² d (Semantics.body UnLet ρ₃) (reify vl^Tm) r) ⟩
   fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₃) r)
     ∎
 unLetSub-body [] σ t ρᴿ = unLetSub t ρᴿ
 unLetSub-body Ξ@(x ∷ xs) σ {Γ} {Δ} {Θ} t {ρ₁} {ρ₃} {ρ₂} ρᴿ = unLetSub t ρ′ᴿ where

  ρ₁₁ : (Ξ ─Env) (Tm d ∞) (Ξ ++ Θ)
  ρ₁₁ = th^Env th^Tm (base vl^Tm) (pack (injectˡ Θ))
  ρ₁₂ = th^Env th^Tm ρ₂ (th^Env th^Var (base vl^Var) (pack (injectʳ Ξ)))

  ρ₁₃ = pack (`var ∘ injectˡ Θ {Ξ}) >> th^Env th^Tm ρ₂ (pack (injectʳ Ξ))

  eq₁₁ᴿ : All Eqᴿ _ ρ₁₁ (pack (`var ∘ injectˡ Θ))
  lookupᴿ eq₁₁ᴿ k = cong (ren (pack (injectˡ Θ))) (lookup-base^Tm k)

  eq₁₂ᴿ : All Eqᴿ _ ρ₁₂ (th^Env th^Tm ρ₂ (pack (injectʳ Ξ)))
  lookupᴿ eq₁₂ᴿ k =
    Simulation.sim RenExt (packᴿ (cong (injectʳ Ξ) ∘ lookup-base^Var)) (lookup ρ₂ k)

  eq₁ᴿ : All Eqᴿ _ (ρ₁₁ >> ρ₁₂) ρ₁₃
  eq₁ᴿ = eq₁₁ᴿ >>ᴿ eq₁₂ᴿ

  ρ₂₁ = th^Env th^Var (base vl^Var) (pack (injectʳ Ξ))

  ρ′ᴿ : All Eqᴿ _ (sub (freshˡ vl^Tm Θ  >> th^Env th^Tm ρ₂ (freshʳ vl^Var Ξ))
                    <$> (freshˡ vl^Tm Δ >> th^Env th^Tm  ρ₁ (freshʳ vl^Var Ξ)))
                  (freshˡ vl^Tm Θ >> th^Env th^Tm ρ₃ (freshʳ vl^Var Ξ))
  lookupᴿ ρ′ᴿ k with split Ξ k
  ... | inj₁ kˡ = begin
    sub (ρ₁₁ >> ρ₁₂) (ren (pack (injectˡ Δ))(lookup (base vl^Tm) kˡ))
      ≡⟨ cong (sub (ρ₁₁ >> ρ₁₂) ∘ ren (pack (injectˡ Δ))) (lookup-base^Tm kˡ) ⟩
    lookup (ρ₁₁ >> ρ₁₂) (injectˡ Δ kˡ)
      ≡⟨ injectˡ->> ρ₁₁ ρ₁₂ kˡ ⟩
    ren (pack (injectˡ Θ)) (lookup (base vl^Tm) kˡ)
      ≡⟨ cong (ren (pack (injectˡ Θ))) (lookup-base^Tm kˡ) ⟩
    `var (injectˡ Θ kˡ)
      ≡⟨ cong (ren (pack (injectˡ Θ))) (sym (lookup-base^Tm kˡ)) ⟩
    ren (pack (injectˡ Θ)) (lookup (base vl^Tm) kˡ)
      ∎
  ... | inj₂ kʳ = begin
    sub (ρ₁₁ >> ρ₁₂) (ren ρ₂₁ (lookup ρ₁ kʳ))
      ≡⟨ Simulation.sim SubExt eq₁ᴿ (ren ρ₂₁ (lookup ρ₁ kʳ)) ⟩
    sub ρ₁₃ (ren ρ₂₁ (lookup ρ₁ kʳ))
      ≡⟨ cong (sub ρ₁₃) (Simulation.sim RenExt eq₂ᴿ  (lookup ρ₁ kʳ)) ⟩
    sub ρ₁₃ (ren (pack (injectʳ Ξ)) (lookup ρ₁ kʳ))
      ≡⟨ Fusion.fusion (F.RenSub d) eqᴿ (lookup ρ₁ kʳ) ⟩
    sub (th^Env th^Tm ρ₂ (pack (injectʳ Ξ))) (lookup ρ₁ kʳ)
      ≡⟨ sym (Fusion.fusion (SubRen d) eq₃ᴿ (lookup ρ₁ kʳ)) ⟩
    ren ρ₃₁ (sub ρ₂ (lookup ρ₁ kʳ))
      ≡⟨ cong (ren ρ₃₁) (lookupᴿ ρᴿ kʳ) ⟩
    ren ρ₃₁ (lookup ρ₃ kʳ)
      ∎ where

    eq₂ᴿ : All Eqᴿ _ ρ₂₁ (pack (injectʳ Ξ))
    lookupᴿ eq₂ᴿ k = cong (injectʳ Ξ) (lookup-base^Var k)

    ρ₃₁ = th^Env th^Var (base vl^Var) (pack (injectʳ Ξ))

    eq₃ᴿ : All Eqᴿ _ (ren ρ₃₁ <$> ρ₂) (th^Env th^Tm ρ₂ (pack (injectʳ Ξ)))
    lookupᴿ eq₃ᴿ k =
      Simulation.sim RenExt (packᴿ (cong (injectʳ Ξ) ∘ lookup-base^Var)) (lookup ρ₂ k)

    eqᴿ : All Eqᴿ _ (select (pack (injectʳ Ξ)) ρ₁₃) (th^Env th^Tm ρ₂ (pack (injectʳ Ξ)))
    lookupᴿ eqᴿ k with split Ξ (injectʳ Ξ k) | split-injectʳ Ξ k
    lookupᴿ eqᴿ k | .(inj₂ k) | refl = refl
\end{code}

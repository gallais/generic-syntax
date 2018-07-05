module Generic.Fusion.Syntactic where

open import Size
open import Data.List hiding (lookup)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function

open import var hiding (_<$>_)
open import varlike
open import environment
open import rel
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Simulation
import Generic.Simulation.Syntactic as S
open import Generic.Zip
open import Generic.Identity
open import Generic.Fusion
import Generic.Fusion.Specialised.Propositional as FusProp

module _ {I : Set} (d : Desc I) where

 Ren² : Fus (λ ρ₁ → ∀[ Eq^R ] ∘ (select ρ₁)) Eq^R Eq^R d Renaming Renaming Renaming
 Ren² = FusProp.ren-sem d Renaming $ λ b ρ^R zp →
   cong `con $ zip^reify Eq^R (reify^R Eq^R Eq^R (vl^Refl vl^Var)) d zp

 ren² : {Γ Δ Θ : List I} {i : I} {s : Size} → (t : Tm d s i Γ) (ρ₁ : Thinning Γ Δ) (ρ₂ : Thinning Δ Θ) →
        ren ρ₂ (ren ρ₁ t) ≡ ren (select ρ₁ ρ₂) t
 ren² t ρ₁ ρ₂ = Fus.fus Ren² (pack^R (λ _ → refl)) t

 RenSub : Fus (λ ρ₁ → ∀[ Eq^R ] ∘ (select ρ₁)) Eq^R Eq^R d Renaming Substitution Substitution
 RenSub = FusProp.ren-sem d Substitution $ λ b ρ^R zp →
   cong `con $ zip^reify Eq^R (reify^R Eq^R Eq^R (vl^Refl vl^Tm)) d zp

 rensub :  {Γ Δ Θ : List I} {i : I} {s : Size} → (t : Tm d s i Γ) (ρ₁ : Thinning Γ Δ) (ρ₂ : (Δ ─Env) (Tm d ∞) Θ) →
           sub ρ₂ (ren ρ₁ t) ≡ sub (select ρ₁ ρ₂) t
 rensub t ρ₁ ρ₂ = Fus.fus RenSub (pack^R (λ _ → refl)) t

 SubRen : Fus (λ ρ₁ ρ₂ → ∀[ Eq^R ] (ren ρ₂ <$> ρ₁)) VarTm^R Eq^R d Substitution Renaming Substitution
 Fus.quote₁  SubRen = λ _ → id
 Fus.vl^𝓥₁  SubRen = vl^Tm
 Fus.th^R    SubRen {ρ₁ = ρ₁} {ρ₂} {ρ₃} = λ σ ρ^R → pack^R $ λ k →
   begin
     ren (select ρ₂ σ) (lookup ρ₁ k) ≡⟨ sym $ ren² (lookup ρ₁ k) ρ₂ σ ⟩
     ren σ (ren ρ₂ (lookup ρ₁ k))    ≡⟨ cong (ren σ) (lookup^R ρ^R k) ⟩
     ren σ (lookup ρ₃ k)
   ∎
 Fus.>>^R   SubRen {ρ₁ = ρ₁} = subBodyEnv Renaming Ren² (λ σ t → refl) ρ₁
 Fus.var^R   SubRen = λ ρ^R v → lookup^R ρ^R v
 Fus.alg^R   SubRen {ρ₁ = ρ₁} {ρ₂} {ρ₃} b ρ^R = λ zipped → cong `con $
   let v₁ = fmap d (Sem.body Substitution ρ₁) b
       v₃ = fmap d (Sem.body Substitution ρ₃) b in
   begin
     fmap d (reify vl^Var) (fmap d (Sem.body Renaming ρ₂) (fmap d (reify vl^Tm) v₁))
         ≡⟨ cong (fmap d (reify vl^Var)) (fmap² d (reify vl^Tm) (Sem.body Renaming ρ₂) v₁) ⟩
     fmap d (reify vl^Var) (fmap d (λ Φ i → (Sem.body Renaming ρ₂ Φ i) ∘ (reify vl^Tm Φ i)) v₁)
         ≡⟨ zip^reify VarTm^R (reify^R VarTm^R Eq^R vl^VarTm) d zipped ⟩
      fmap d (reify vl^Tm) v₃
   ∎

 subren :  {Γ Δ Θ : List I} {i : I} {s : Size} → ∀ (t : Tm d s i Γ) (ρ₁ : (Γ ─Env) (Tm d ∞) Δ) (ρ₂ : Thinning Δ Θ) →
           ren ρ₂ (sub ρ₁ t) ≡ sub (ren ρ₂ <$> ρ₁) t
 subren t ρ₁ ρ₂ = Fus.fus SubRen (pack^R (λ k → refl)) t


 Sub² : Fus (λ ρ₁ ρ₂ → ∀[ Eq^R ] (sub ρ₂ <$> ρ₁)) Eq^R Eq^R d Substitution Substitution Substitution
 Fus.quote₁ Sub² = λ _ t → t
 Fus.vl^𝓥₁ Sub² = vl^Tm
 Fus.th^R Sub² {ρ₁ = ρ₁} {ρ₂} {ρ₃} = λ σ ρ^R → pack^R $ λ k →
   begin
     sub (ren σ <$> ρ₂) (lookup ρ₁ k) ≡⟨ sym $ subren (lookup ρ₁ k) ρ₂ σ ⟩
     ren σ (sub ρ₂ (lookup ρ₁ k))     ≡⟨ cong (ren σ) (lookup^R ρ^R k)   ⟩
     ren σ (lookup ρ₃ k)
   ∎
 Fus.>>^R Sub² {ρ₁ = ρ₁} = subBodyEnv Substitution RenSub (λ σ t → refl) ρ₁
 Fus.var^R Sub² = λ ρ^R v → lookup^R ρ^R v
 Fus.alg^R Sub² {ρ₁ = ρ₁} {ρ₂} {ρ₃} b ρ^R = λ zipped → cong `con $
   let v₁ = fmap d (Sem.body Substitution ρ₁) b
       v₃ = fmap d (Sem.body Substitution ρ₃) b in
   begin
     fmap d (reify vl^Tm) (fmap d (Sem.body Substitution ρ₂) (fmap d (reify vl^Tm) v₁))
         ≡⟨ cong (fmap d (reify vl^Tm)) (fmap² d (reify vl^Tm) (Sem.body Substitution ρ₂) v₁) ⟩
     fmap d (reify vl^Tm) (fmap d (λ Φ i → (Sem.body Substitution ρ₂ Φ i) ∘ (reify vl^Tm Φ i)) v₁)
         ≡⟨ zip^reify Eq^R (reify^R Eq^R Eq^R (vl^Refl vl^Tm)) d zipped ⟩
      fmap d (reify vl^Tm) v₃
   ∎

 sub² :  {Γ Δ Θ : List I} {i : I} {s : Size} → ∀ (t : Tm d s i Γ) (ρ₁ : (Γ ─Env) (Tm d ∞) Δ) (ρ₂ : (Δ ─Env) (Tm d ∞) Θ) →
         sub ρ₂ (sub ρ₁ t) ≡ sub (sub ρ₂ <$> ρ₁) t
 sub² t ρ₁ ρ₂ = Fus.fus Sub² (pack^R (λ k → refl)) t




 ren-sub-fusion^R : ∀ {Δ Γ Θ} (σ : (Δ ─Env) (Tm d ∞) Γ) (ρ : Thinning Γ Θ) →
   ∀[ Eq^R ] (select (lift vl^Var Δ ρ) (base vl^Tm <+> (ren ρ <$> σ)))
             (ren ρ <$> (base vl^Tm <+> σ))
 lookup^R (ren-sub-fusion^R {Δ} {Γ} {Θ} σ ρ) k with split Δ k
 ... | inj₁ k₁ = begin
   lookup (base vl^Tm <+> (ren ρ <$> σ)) (injectˡ Θ (lookup (base vl^Var) k₁))
     ≡⟨ injectˡ-<+> Θ (base vl^Tm) (ren ρ <$> σ) (lookup (base vl^Var) k₁) ⟩
   lookup {𝓥 = Tm d ∞} (ren ρ <$> σ) (lookup (base vl^Var) k₁)
     ≡⟨ cong (lookup {𝓥 = Tm d ∞} (ren ρ <$> σ)) (lookup-base^Var k₁) ⟩
   ren ρ (lookup σ k₁)
     ≡⟨ cong (ren ρ) (sym (injectˡ-<+> Γ (base vl^Tm) σ k₁)) ⟩
   ren ρ (lookup (base vl^Tm <+> σ) (injectˡ Γ k₁))
     ∎
 ... | inj₂ k₂ = begin
   lookup (base vl^Tm <+> (ren ρ <$> σ)) (injectʳ Δ (lookup (base vl^Var) (lookup ρ k₂)))
     ≡⟨ injectʳ-<+> Δ (base vl^Tm) (ren ρ <$> σ) (lookup (base vl^Var) (lookup ρ k₂)) ⟩
   lookup (base vl^Tm) (lookup (base vl^Var) (lookup ρ k₂))
     ≡⟨ lookup-base^Tm _ ⟩
   `var (lookup (base vl^Var) (lookup ρ k₂))
     ≡⟨ cong `var (lookup-base^Var (lookup ρ k₂)) ⟩
   ren ρ (`var k₂)
     ≡⟨ cong (ren ρ) (sym (lookup-base^Tm k₂)) ⟩
   ren ρ (lookup (base vl^Tm) k₂)
     ≡⟨ cong (ren ρ) (sym (injectʳ-<+> Δ (base vl^Tm) σ k₂)) ⟩
   ren ρ (lookup (base vl^Tm <+> σ) (injectʳ Δ k₂))
     ∎

-- Corollary

 renβ : ∀ {Δ Γ Θ s i} (b : Scope (Tm d s) Δ i Γ) (σ : (Δ ─Env) (Tm d ∞) Γ) (ρ : Thinning Γ Θ) →
        sub (base vl^Tm <+> (ren ρ <$> σ)) (ren (lift vl^Var Δ ρ) b)
        ≡ ren ρ (sub (base vl^Tm <+> σ) b)
 renβ {Δ} b σ ρ = begin
   sub (base vl^Tm <+> (ren ρ <$> σ)) (ren (lift vl^Var Δ ρ) b)
     ≡⟨ Fus.fus RenSub (ren-sub-fusion^R σ ρ) b ⟩
   sub (ren ρ <$> (base vl^Tm <+> σ)) b
     ≡⟨ sym (subren b (base vl^Tm <+> σ) ρ) ⟩
   ren ρ (sub (base vl^Tm <+> σ) b)
     ∎

 sub-sub-fusion^R : ∀ {Δ Γ Θ} (σ : (Δ ─Env) (Tm d ∞) Γ) (ρ : (Γ ─Env) (Tm d ∞) Θ) →
   ∀[ Eq^R {I} {Tm d ∞} ] (sub (base vl^Tm {Θ} <+> (sub ρ <$> σ)) <$> lift vl^Tm Δ {Γ} ρ)
                          (sub ρ <$> (base vl^Tm <+> σ))
 lookup^R (sub-sub-fusion^R {Δ} {Γ} {Θ} σ ρ) k with split Δ k
 ... | inj₁ k₁ = begin
   sub (base vl^Tm <+> (sub ρ <$> σ)) (ren (pack (injectˡ Θ)) (lookup (base vl^Tm) k₁))
     ≡⟨ cong (λ v → sub (base vl^Tm <+> (sub ρ <$> σ)) (ren (pack (injectˡ Θ)) v)) (lookup-base^Tm k₁) ⟩
   lookup (base vl^Tm <+> (sub ρ <$> σ)) (injectˡ Θ k₁)
     ≡⟨ injectˡ-<+> Θ (base vl^Tm) (sub ρ <$> σ) k₁ ⟩
   sub ρ (lookup σ k₁)
     ≡⟨ cong (sub ρ) (sym (injectˡ-<+> Γ (base vl^Tm) σ k₁)) ⟩
   sub ρ (lookup (base vl^Tm <+> σ) (injectˡ Γ k₁))
     ∎
 ... | inj₂ k₂ = begin
   sub (base vl^Tm <+> (sub ρ <$> σ)) (ren (th^Env th^Var (base vl^Var) (pack (injectʳ Δ))) (lookup ρ k₂))
     ≡⟨ Fus.fus RenSub (pack^R (λ v → injectʳ-<+> Δ (base vl^Tm) (sub ρ <$> σ) (lookup (base vl^Var) v))) (lookup ρ k₂) ⟩
   sub (select (base vl^Var) (base vl^Tm)) (lookup ρ k₂)
     ≡⟨ Sim.sim S.SubExt (pack^R (λ v → cong (lookup (base vl^Tm)) (lookup-base^Var v))) (lookup ρ k₂) ⟩
   sub (base vl^Tm) (lookup ρ k₂)
     ≡⟨ sub-id (lookup ρ k₂) ⟩
   lookup ρ k₂
     ≡⟨ cong (sub ρ) (sym (lookup-base^Tm k₂)) ⟩
   sub ρ (lookup (base vl^Tm) k₂)
     ≡⟨ cong (sub ρ) (sym (injectʳ-<+> Δ (base vl^Tm) σ k₂)) ⟩
   sub ρ (lookup (base vl^Tm <+> σ) (injectʳ Δ k₂))
     ∎

 subβ : ∀ {Δ Γ Θ s i} (b : Scope (Tm d s) Δ i Γ) (σ : (Δ ─Env) (Tm d ∞) Γ) (ρ : (Γ ─Env) (Tm d ∞) Θ) →
        sub (base vl^Tm <+> (sub ρ <$> σ)) (sub (lift vl^Tm Δ ρ) b)
        ≡ sub ρ (sub (base vl^Tm <+> σ) b)
 subβ {Δ} b σ ρ = begin
   sub (base vl^Tm <+> (sub ρ <$> σ)) (sub (lift vl^Tm Δ ρ) b)
     ≡⟨ Fus.fus Sub² (sub-sub-fusion^R σ ρ) b ⟩
   sub (sub ρ <$> (base vl^Tm <+> σ)) b
     ≡⟨ sym (sub² b (base vl^Tm <+> σ) ρ) ⟩
   sub ρ (sub (base vl^Tm <+> σ) b)
     ∎

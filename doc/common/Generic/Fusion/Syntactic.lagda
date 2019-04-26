\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Fusion.Syntactic where

open import Size
open import Data.List hiding (lookup)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function

open import Data.Var hiding (_<$>_)
open import Data.Var.Varlike
open import Data.Environment
open import Data.Relation as Relation
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Simulation as Simulation
import Generic.Simulation.Syntactic as S
open import Generic.Relator as Relator
open import Generic.Identity
open import Generic.Fusion
open import Generic.Fusion.Utils
import Generic.Fusion.Specialised.Propositional as FusProp

module _ {I : Set} (d : Desc I) where

 private
   variable
     Γ Δ Θ : List I
     σ : I
     i : Size

 Ren² : Fusion d Ren Ren Ren (λ Γ Δ ρ₁ → All Eqᴿ Γ ∘ (select ρ₁)) Eqᴿ Eqᴿ
 Ren² = FusProp.ren-sem d Ren $ λ b ρᴿ zp →
   cong `con $ Relator.reifyᴿ Eqᴿ d (Simulation.reifyᴿ Eqᴿ Eqᴿ (vl^Refl vl^Var)) zp

 ren² : (t : Tm d i σ Γ) (ρ₁ : Thinning Γ Δ) (ρ₂ : Thinning Δ Θ) →
        ren ρ₂ (ren ρ₁ t) ≡ ren (select ρ₁ ρ₂) t
 ren² t ρ₁ ρ₂ = Fusion.fusion Ren² Relation.reflᴿ t

 RenSub : Fusion d Ren Sub Sub (λ Γ Δ ρ₁ → All Eqᴿ Γ ∘ (select ρ₁)) Eqᴿ Eqᴿ
 RenSub = FusProp.ren-sem d Sub $ λ b ρᴿ zp →
   cong `con $ Relator.reifyᴿ Eqᴿ d (Simulation.reifyᴿ Eqᴿ Eqᴿ (vl^Refl vl^Tm)) zp

 rensub :  (t : Tm d i σ Γ) (ρ₁ : Thinning Γ Δ) (ρ₂ : (Δ ─Env) (Tm d ∞) Θ) →
           sub ρ₂ (ren ρ₁ t) ≡ sub (select ρ₁ ρ₂) t
 rensub t ρ₁ ρ₂ = Fusion.fusion RenSub Relation.reflᴿ t

 SubRen : Fusion d Sub Ren Sub (λ Γ Δ ρ₁ ρ₂ → All Eqᴿ Γ (ren ρ₂ <$> ρ₁)) VarTmᴿ Eqᴿ
 Fusion.reifyᴬ  SubRen = λ _ → id
 Fusion.vl^𝓥ᴬ  SubRen = vl^Tm
 Fusion.th^𝓔ᴿ    SubRen {ρᴬ = ρ₁} {ρᴮ = ρ₂} {ρ₃} = λ ρᴿ σ → packᴿ $ λ k →
   begin
     ren (select ρ₂ σ) (lookup ρ₁ k) ≡⟨ sym $ ren² (lookup ρ₁ k) ρ₂ σ ⟩
     ren σ (ren ρ₂ (lookup ρ₁ k))    ≡⟨ cong (ren σ) (lookupᴿ ρᴿ k) ⟩
     ren σ (lookup ρ₃ k)
   ∎
 Fusion._>>ᴿ_  SubRen {ρᴬ = ρ₁} = subBodyEnv Ren Ren² (λ σ t → refl) ρ₁
 Fusion.varᴿ   SubRen = λ ρᴿ v → lookupᴿ ρᴿ v
 Fusion.algᴿ   SubRen {ρᴬ = ρ₁} {ρᴮ = ρ₂} {ρᴬᴮ = ρ₃} ρᴿ b = λ zipped → cong `con $
   let v₁ = fmap d (Semantics.body Sub ρ₁) b
       v₃ = fmap d (Semantics.body Sub ρ₃) b in
   begin
     fmap d (reify vl^Var) (fmap d (Semantics.body Ren ρ₂) (fmap d (reify vl^Tm) v₁))
         ≡⟨ cong (fmap d (reify vl^Var)) (fmap² d (reify vl^Tm) (Semantics.body Ren ρ₂) v₁) ⟩
     fmap d (reify vl^Var) (fmap d (λ Φ i → (Semantics.body Ren ρ₂ Φ i) ∘ (reify vl^Tm Φ i)) v₁)
         ≡⟨ Relator.reifyᴿ VarTmᴿ d (Simulation.reifyᴿ VarTmᴿ Eqᴿ vl^VarTm) zipped ⟩
      fmap d (reify vl^Tm) v₃
   ∎

\end{code}
%<*subren>
\begin{code}
 subren :  (t : Tm d i σ Γ) (ρ₁ : (Γ ─Env) (Tm d ∞) Δ) (ρ₂ : Thinning Δ Θ) →
           ren ρ₂ (sub ρ₁ t) ≡ sub (ren ρ₂ <$> ρ₁) t
\end{code}
%</subren>
\begin{code}
 subren t ρ₁ ρ₂ = Fusion.fusion SubRen Relation.reflᴿ t

 Sub² : Fusion d Sub Sub Sub (λ Γ Δ ρ₁ ρ₂ → All Eqᴿ Γ (sub ρ₂ <$> ρ₁)) Eqᴿ Eqᴿ
 Fusion.reifyᴬ Sub² = λ _ t → t
 Fusion.vl^𝓥ᴬ Sub² = vl^Tm
 Fusion.th^𝓔ᴿ Sub² {ρᴬ = ρ₁} {ρᴮ = ρ₂} {ρᴬᴮ = ρ₃} = λ ρᴿ σ → packᴿ $ λ k →
   begin
     sub (ren σ <$> ρ₂) (lookup ρ₁ k) ≡⟨ sym $ subren (lookup ρ₁ k) ρ₂ σ ⟩
     ren σ (sub ρ₂ (lookup ρ₁ k))     ≡⟨ cong (ren σ) (lookupᴿ ρᴿ k)   ⟩
     ren σ (lookup ρ₃ k)
   ∎
 Fusion._>>ᴿ_ Sub² {ρᴬ = ρ₁} = subBodyEnv Sub RenSub (λ σ t → refl) ρ₁
 Fusion.varᴿ Sub² = λ ρᴿ v → lookupᴿ ρᴿ v
 Fusion.algᴿ Sub² {ρᴬ = ρ₁} {ρᴮ = ρ₂} {ρᴬᴮ = ρ₃} ρᴿ b = λ zipped → cong `con $
   let v₁ = fmap d (Semantics.body Sub ρ₁) b
       v₃ = fmap d (Semantics.body Sub ρ₃) b in
   begin
     fmap d (reify vl^Tm) (fmap d (Semantics.body Sub ρ₂) (fmap d (reify vl^Tm) v₁))
         ≡⟨ cong (fmap d (reify vl^Tm)) (fmap² d (reify vl^Tm) (Semantics.body Sub ρ₂) v₁) ⟩
     fmap d (reify vl^Tm) (fmap d (λ Φ i → (Semantics.body Sub ρ₂ Φ i) ∘ (reify vl^Tm Φ i)) v₁)
         ≡⟨ Relator.reifyᴿ Eqᴿ d (Simulation.reifyᴿ Eqᴿ Eqᴿ (vl^Refl vl^Tm)) zipped ⟩
      fmap d (reify vl^Tm) v₃
   ∎

\end{code}
%<*subsub>
\begin{code}
 sub² :  (t : Tm d i σ Γ) (ρ₁ : (Γ ─Env) (Tm d ∞) Δ) (ρ₂ : (Δ ─Env) (Tm d ∞) Θ) →
         sub ρ₂ (sub ρ₁ t) ≡ sub (sub ρ₂ <$> ρ₁) t
\end{code}
%</subsub>
\begin{code}
 sub² t ρ₁ ρ₂ = Fusion.fusion Sub² Relation.reflᴿ t

 ren-sub-fusionᴿ : ∀ {Δ Γ Θ} (σ : (Δ ─Env) (Tm d ∞) Γ) (ρ : Thinning Γ Θ) →
   All Eqᴿ _ (select (lift vl^Var Δ ρ) (base vl^Tm <+> (ren ρ <$> σ)))
             (ren ρ <$> (base vl^Tm <+> σ))
 lookupᴿ (ren-sub-fusionᴿ {Δ} {Γ} {Θ} σ ρ) k with split Δ k
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
     ≡⟨ Fusion.fusion RenSub (ren-sub-fusionᴿ σ ρ) b ⟩
   sub (ren ρ <$> (base vl^Tm <+> σ)) b
     ≡⟨ sym (subren b (base vl^Tm <+> σ) ρ) ⟩
   ren ρ (sub (base vl^Tm <+> σ) b)
     ∎

 sub-sub-fusionᴿ : ∀ {Δ Γ Θ} (σ : (Δ ─Env) (Tm d ∞) Γ) (ρ : (Γ ─Env) (Tm d ∞) Θ) →
   All (Eqᴿ {I} {Tm d ∞}) _ (sub (base vl^Tm {Θ} <+> (sub ρ <$> σ)) <$> lift vl^Tm Δ ρ)
                          (sub ρ <$> (base vl^Tm <+> σ))
 lookupᴿ (sub-sub-fusionᴿ {Δ} {Γ} {Θ} σ ρ) k with split Δ k
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
     ≡⟨ Fusion.fusion RenSub (packᴿ (λ v → injectʳ-<+> Δ (base vl^Tm) (sub ρ <$> σ) (lookup (base vl^Var) v))) (lookup ρ k₂) ⟩
   sub (select (base vl^Var) (base vl^Tm)) (lookup ρ k₂)
     ≡⟨ Simulation.sim S.SubExt (packᴿ (λ v → cong (lookup (base vl^Tm)) (lookup-base^Var v))) (lookup ρ k₂) ⟩
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
     ≡⟨ Fusion.fusion Sub² (sub-sub-fusionᴿ σ ρ) b ⟩
   sub (sub ρ <$> (base vl^Tm <+> σ)) b
     ≡⟨ sym (sub² b (base vl^Tm <+> σ) ρ) ⟩
   sub ρ (sub (base vl^Tm <+> σ) b)
     ∎
\end{code}

\begin{code}
module Generic.Examples.ElaborationLet where

open import Size
open import Data.Bool
open import Data.Product
open import Data.List.Base hiding ([_])
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import indexed
open import var hiding (_<$>_)
open import rel
open import varlike
open import environment
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Simulation
open import Generic.Fusion as F
open import Generic.Zip

module _ {I : Set} where
\end{code}
%<*letcode>
\begin{code}
 Let : Desc I
 Let = `σ (I × I) $ uncurry λ σ τ →
       `X [] σ (`X (σ ∷ []) τ (`∎ τ))
\end{code}
%</letcode>
\begin{code}
module _ {I : Set} {d : Desc I} where
\end{code}
%<*unletcode>
\begin{code}
 UnLet : Sem (d `+ Let) (Tm d ∞) (Tm d ∞)
 Sem.th^𝓥  UnLet = th^Tm
 Sem.var   UnLet = id
 Sem.alg   UnLet = case (Sem.alg Substitution) λ where
   (_ , e , t , refl) → extract t (ε ∙ e)
\end{code}
%</unletcode>
\begin{code}
 unLet : ∀{Γ Δ σ s} → (Γ ─Env) (Tm d ∞) Δ → Tm (d `+ Let) s σ Γ → Tm d ∞ σ Δ
 unLet ρ t = Sem.sem UnLet ρ t
\end{code}
%<*unlet>
\begin{code}
 unlet : {i : I} → [ Tm (d `+ Let) ∞ i ⟶ Tm d ∞ i ]
 unlet = Sem.sem UnLet (pack `var)
\end{code}
%</unlet>

\begin{code}
 open ≡-Reasoning

 proj₂-eq : ∀ {a b} {A : Set a} {B : A → Set b} {x : A} {b₁ b₂ : B x} →
            (Σ A B ∋ x , b₁) ≡ (x , b₂) → b₁ ≡ b₂
 proj₂-eq refl = refl

 RenUnLet : Fus (λ ρ₁ ρ₂ → ∀[ Eq^R ] (select ρ₁ ρ₂)) Eq^R Eq^R
            (d `+ Let) (d `+ Let) Renaming UnLet UnLet
 Fus.quote₁ RenUnLet = λ σ t → t
 Fus.vl^𝓥₁ RenUnLet = vl^Var
 Fus.th^R   RenUnLet = λ σ ρ^R → pack^R (cong (ren σ) ∘ lookup^R ρ^R)
 Fus.>>^R   RenUnLet = thBodyEnv
 Fus.var^R  RenUnLet = λ ρ^R → lookup^R ρ^R
 Fus.alg^R RenUnLet (false , (_ , e , t , refl)) ρ^R (refl , refl , eq^e , eq^t , _)
   = eq^t (pack id) (ε^R ∙^R eq^e)
 Fus.alg^R RenUnLet {ρ₁ = ρ₁} {ρ₂} {ρ₃} (true , t) ρ^R eq^t
   = cong `con $ begin
     let t′ = fmap d (Sem.body Renaming ρ₁) t in
     fmap d (reify vl^Tm) (fmap d (Sem.body UnLet ρ₂) (fmap d (reify vl^Var) t′))
       ≡⟨ cong (fmap d (reify vl^Tm)) (fmap² d (reify vl^Var) (Sem.body UnLet ρ₂) t′) ⟩
     fmap d (reify vl^Tm) (fmap d (λ Δ i → (Sem.body UnLet ρ₂ Δ i) ∘ reify vl^Var Δ i) t′)
       ≡⟨ proj₂-eq $ zip^reify Eq^R (reify^R Eq^R Eq^R (vl^Refl vl^Tm)) (d `+ Let) eq^t ⟩
     fmap d (reify vl^Tm) (fmap d (Sem.body UnLet ρ₃) t)
       ∎


 UnLetSub : Fus (λ ρ₁ ρ₂ → ∀[ Eq^R ] (sub ρ₂ <$> ρ₁)) Eq^R Eq^R
            (d `+ Let) d UnLet Substitution UnLet
 Fus.quote₁ UnLetSub = λ σ t → t
 Fus.vl^𝓥₁ UnLetSub = vl^Tm
 Fus.th^R   UnLetSub {ρ₁ = ρ₁} {ρ₂} {ρ₃} = λ σ ρ^R → pack^R λ v → begin
   sub (th^Env th^Tm ρ₂ σ) (lookup ρ₁ v)
     ≡⟨ sym (subren d (lookup ρ₁ v) ρ₂ σ) ⟩
   ren σ (sub ρ₂ (lookup ρ₁ v))
     ≡⟨ cong (ren σ) (lookup^R ρ^R v) ⟩
   ren σ (lookup ρ₃ v)
     ∎
 Fus.>>^R   UnLetSub {ρ₁ = ρ₁} = subBodyEnv Substitution (F.RenSub d) (λ σ t → refl) ρ₁
 Fus.var^R  UnLetSub = λ ρ^R → lookup^R ρ^R
 Fus.alg^R  UnLetSub {Γ} {Δ} {Θ} {Ξ} {ρ₁ = ρ₁} {ρ₂} {ρ₃} (false , (_ , e , t , refl)) ρ^R (refl , refl , eq^e , eq^t , _)
   = begin
     sub ρ₂ (unLet ((ε ∙ unLet ρ₁ e) >> th^Env th^Tm ρ₁ (pack id)) t)
       ≡⟨ {!!} ⟩
     sub ρ₂ (unLet ? t)
       ≡⟨ eq^t ? ? ⟩
     unLet ((ε ∙ unLet ρ₃ e) >> th^Env th^Tm ρ₃ (pack id)) t
       ∎
 Fus.alg^R  UnLetSub {ρ₁ = ρ₁} {ρ₂} {ρ₃} (true , t) ρ^R eq^t
   = cong `con $ begin
     let t′ = fmap d (Sem.body UnLet ρ₁) t in
     fmap d (reify vl^Tm) (fmap d (Sem.body Substitution ρ₂)(fmap d (reify vl^Tm) t′))
       ≡⟨ cong (fmap d (reify vl^Tm)) (fmap² d (reify vl^Tm) (Sem.body Substitution ρ₂) t′) ⟩
     fmap d (reify vl^Tm) (fmap d (λ Δ i → Sem.body Substitution ρ₂ Δ i ∘ reify vl^Tm Δ i) t′)
       ≡⟨ proj₂-eq $ zip^reify Eq^R (reify^R Eq^R Eq^R (vl^Refl vl^Tm)) (d `+ Let) eq^t ⟩
     fmap d (reify vl^Tm) (fmap d (Sem.body UnLet ρ₃) t)
       ∎


{-
 UnLetRen : Fus (λ ρ₁ ρ₂ → ∀[ Eq^R ] (ren ρ₂ <$> ρ₁)) VarTm^R Eq^R
            (d `+ Let) d UnLet Renaming UnLet
 Fus.quote₁  UnLetRen = λ σ t → t
 Fus.vl^𝓥₁  UnLetRen = vl^Tm
 Fus.th^R    UnLetRen {ρ₁ = ρ₁} {ρ₂} {ρ₃} = λ σ ρ^R → pack^R λ v → begin
   ren (select ρ₂ σ) (lookup ρ₁ v)
     ≡⟨ sym (ren² d (lookup ρ₁ v) ρ₂ σ) ⟩
   ren σ (ren ρ₂ (lookup ρ₁ v))
     ≡⟨ cong (ren σ) (lookup^R ρ^R v) ⟩
   ren σ (lookup ρ₃ v)
     ∎
 Fus.>>^R    UnLetRen {ρ₁ = ρ₁} = subBodyEnv Renaming (Ren² d) (λ σ t → refl) ρ₁
 Fus.var^R   UnLetRen = λ ρ^R → lookup^R ρ^R
 Fus.alg^R   UnLetRen {ρ₁ = ρ₁} {ρ₂} {ρ₃} (false , (_ , e , t , refl)) ρ^R (refl , refl , eq^e , eq^t , _)
   = begin
   ren ρ₂ (unLet ((ε ∙ unLet ρ₁ e) >> th^Env th^Tm ρ₁ (pack id)) t)
     ≡⟨ {!!} ⟩
   ren ((ε ∙ {!!}) >> th^Env th^Var ρ₂ (pack id)) (unLet {!freshˡ (UnLetRen .Fus.vl^𝓥₁) .Δ >>
                                                           th^Env (Sem.th^𝓥 UnLet) ρ₁
                                                           (freshʳ vl^Var
                                                            (fmap (d `+ Let) (Sem.body UnLet ρ₁)
                                                             (false , .proj₁ , e , t , refl) .proj₂ .proj₁ .proj₁
                                                             ∷ []))!} t)
     ≡⟨ eq^t (pack id) (ε^R ∙^R {!!}) ⟩
   unLet ((ε ∙ unLet ρ₃ e) >> th^Env th^Tm ρ₃ (pack id)) t
     ∎
 Fus.alg^R   UnLetRen {ρ₁ = ρ₁} {ρ₂} {ρ₃} (true , t) ρ^R eq^t
   = cong `con $ begin
     let t′ = fmap d (Sem.body UnLet ρ₁) t in
     fmap d (reify vl^Var) (fmap d (Sem.body Renaming ρ₂)(fmap d (reify vl^Tm) t′))
       ≡⟨ cong (fmap d (reify vl^Var)) (fmap² d (reify vl^Tm) (Sem.body Renaming ρ₂) t′) ⟩
     fmap d (reify vl^Var) (fmap d (λ Δ i → Sem.body Renaming ρ₂ Δ i ∘ reify vl^Tm Δ i) t′)
       ≡⟨ proj₂-eq $ zip^reify VarTm^R (reify^R VarTm^R Eq^R vl^VarTm) (d `+ Let) eq^t ⟩
     fmap d (reify vl^Tm) (fmap d (Sem.body UnLet ρ₃) t)
       ∎
-}
{-

      ((ε ∙ Sem.sem UnLet ρ₁ e) >>
       th^Env (λ {i} {a} t₁ {a₁} ρ → Sem.sem Renaming ρ t₁) ρ₁
       (pack (λ {.i} x → x)))
      t)


 unLetRen : ∀ {Γ Δ Θ σ s} (t : Tm (d `+ Let) s σ Γ) {ρ₁ ρ₃} {ρ₂ : Thinning Δ Θ} →
            ∀[ Eq^R ] (ren ρ₂ <$> ρ₁) ρ₃ → ren ρ₂ (unLet ρ₁ t) ≡ unLet ρ₃ t
 unLetRen (`var v) ρ^R = lookup^R ρ^R v
 unLetRen (`con (false , r)) ρ^R = {!!}
 unLetRen (`con (true  , r)) {ρ₁} {ρ₃} {ρ₂} ρ^R = cong `con $ begin
   fmap d (reify vl^Var) (fmap d (Sem.body Renaming ρ₂) (fmap d (reify vl^Tm) (fmap d (Sem.body UnLet ρ₁) r)))
     ≡⟨ {!!} ⟩
   {!!}
     ≡⟨ {!!} ⟩
   fmap d (reify vl^Tm) (fmap d (Sem.body UnLet ρ₃) r)
     ∎

 SubUnLet : Fus (λ ρ₁ ρ₂ → ∀[ Eq^R ] (unLet ρ₂ <$> ρ₁)) Eq^R Eq^R
            (d `+ Let) Substitution UnLet UnLet
 Fus.quote₁ SubUnLet = λ σ t → t
 Fus.vl^𝓥₁ SubUnLet = vl^Tm
 Fus.th^R   SubUnLet {ρ₁ = ρ₁} {ρ₂} {ρ₃} = λ σ ρ^R → pack^R λ v → begin
   Sem.sem UnLet (th^Env th^Tm ρ₂ σ) (lookup ρ₁ v)
     ≡⟨ sym (unLetRen (lookup ρ₁ v) (pack^R λ v → refl)) ⟩
   ren σ (unLet ρ₂ (lookup ρ₁ v))
     ≡⟨ cong (ren σ) (lookup^R ρ^R v) ⟩
   ren σ (lookup ρ₃ v)
    ∎
 Fus.>>^R   SubUnLet {ρ₁ = ρ₁} = subBodyEnv UnLet RenUnLet (λ σ t → refl) ρ₁
 Fus.var^R  SubUnLet = λ ρ^R → lookup^R ρ^R
 Fus.alg^R  SubUnLet (false , (_ , e , t , refl)) ρ^R (refl , refl , eq^e , eq^t , _)
   = eq^t (pack id) (ε^R ∙^R eq^e)
 Fus.alg^R  SubUnLet {ρ₁ = ρ₁} {ρ₂} {ρ₃} (true , t) ρ^R eq^t
   = cong `con $ begin
     let t′ = fmap d (Sem.body Substitution ρ₁) t in
     fmap d (reify vl^Tm) (fmap d (Sem.body UnLet ρ₂) (fmap d (reify vl^Tm) t′))
       ≡⟨ cong (fmap d (reify vl^Tm)) (fmap² d (reify vl^Tm) (Sem.body UnLet ρ₂) t′) ⟩
     fmap d (reify vl^Tm) (fmap d (λ Δ i → Sem.body UnLet ρ₂ Δ i ∘ reify vl^Tm Δ i) t′)
       ≡⟨ proj₂-eq $ zip^reify Eq^R (reify^R Eq^R Eq^R (vl^Refl vl^Tm)) (d `+ Let) eq^t ⟩
     fmap d (reify vl^Tm) (fmap d (Sem.body UnLet ρ₃) t)
       ∎
-}
\end{code}

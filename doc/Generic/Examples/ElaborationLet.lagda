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
open import Generic.Identity
open import Generic.Simulation as S
open import Generic.Fusion as F
open import Generic.Zip

module _ {I : Set} where
\end{code}
%<*letcode>
\begin{code}
 Let : Desc I
 Let =  `σ (I × I) $ uncurry λ σ τ →
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
 Sem.alg   UnLet =
   case (Sem.alg Substitution) λ where
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
            (d `+ Let) Renaming UnLet UnLet
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

 unLetRen : ∀ {Γ Δ Θ σ s} (t : Tm (d `+ Let) s σ Γ) {ρ₁ ρ₃} {ρ₂ : Thinning Δ Θ} →
            ∀[ Eq^R ] (ren ρ₂ <$> ρ₁) ρ₃ → ren ρ₂ (unLet ρ₁ t) ≡ unLet ρ₃ t
 unLetRen-body :
   ∀ Ξ σ {Γ Δ Θ s} (t : Scope (Tm (d `+ Let) s) Ξ σ Γ) {ρ₁ ρ₃} {ρ₂ : Thinning Δ Θ} →
   ∀[ Eq^R ] (ren ρ₂ <$> ρ₁) ρ₃ →
   reify vl^Var Ξ σ (Sem.body Renaming ρ₂ Ξ σ (reify vl^Tm Ξ σ (Sem.body UnLet ρ₁ Ξ σ t)))
   ≡ reify vl^Tm Ξ σ (Sem.body UnLet ρ₃ Ξ σ t)

 unLetRen (`var v) ρ^R = lookup^R ρ^R v
 unLetRen (`con (false , (σ , τ) , e , t , refl)) {ρ₁} {ρ₃} {ρ₂} ρ^R = unLetRen t $ pack^R $ λ where
   z     → unLetRen e ρ^R
   (s v) → begin
     ren ρ₂ (ren (pack id) (lookup ρ₁ v))
       ≡⟨ cong (ren ρ₂) (ren-id′ (lookup ρ₁ v)) ⟩
     ren ρ₂ (lookup ρ₁ v)
       ≡⟨ lookup^R ρ^R v ⟩
     lookup ρ₃ v
       ≡⟨ sym (ren-id′ (lookup ρ₃ v)) ⟩
     ren (pack id) (lookup ρ₃ v)
       ∎
 unLetRen (`con (true  , r)) {ρ₁} {ρ₃} {ρ₂} ρ^R = cong `con $ begin
   fmap d (reify vl^Var) (fmap d (Sem.body Renaming ρ₂) (fmap d (reify vl^Tm) (fmap d (Sem.body UnLet ρ₁) r)))
     ≡⟨ fmap² d (Sem.body Renaming ρ₂) (reify vl^Var) (fmap d (reify vl^Tm) (fmap d (Sem.body UnLet ρ₁) r)) ⟩
   fmap d _ (fmap d (reify vl^Tm) (fmap d (Sem.body UnLet ρ₁) r))
     ≡⟨ fmap² d (reify vl^Tm) _ _ ⟩
   fmap d _ (fmap d (Sem.body UnLet ρ₁) r)
     ≡⟨ fmap² d (Sem.body UnLet ρ₁) _ _ ⟩
   fmap d _ r
     ≡⟨ fmap-ext d (λ Ξ i b → unLetRen-body Ξ i b ρ^R) r ⟩
   fmap d (λ Φ i → reify vl^Tm Φ i ∘ Sem.body UnLet ρ₃ Φ i) r
     ≡⟨ sym (fmap² d (Sem.body UnLet ρ₃) (reify vl^Tm) r) ⟩
   fmap d (reify vl^Tm) (fmap d (Sem.body UnLet ρ₃) r)
     ∎

 unLetRen-body [] σ t ρ^R = unLetRen t ρ^R
 unLetRen-body Ξ@(x ∷ xs) σ {Γ} {Δ} {Θ} t {ρ₁} {ρ₃} {ρ₂} ρ^R = unLetRen t ρ′^R where

  ρ₁₁ : Thinning Ξ (Ξ ++ Θ)
  ρ₁₁ = th^Env th^Var (base vl^Var) (pack (injectˡ Θ))
  ρ₁₂ = th^Env th^Var ρ₂ (th^Env th^Var (base vl^Var) (pack (injectʳ Ξ)))

  ρ₁₃ = pack (injectˡ Θ {Ξ}) >> th^Env th^Var ρ₂ (pack (injectʳ Ξ))

  eq₁₁^R : ∀[ Eq^R ] ρ₁₁ (pack (injectˡ Θ))
  lookup^R eq₁₁^R k = cong (injectˡ Θ) (lookup-base^Var k)

  eq₁₂^R : ∀[ Eq^R ] ρ₁₂ (th^Env th^Var ρ₂ (pack (injectʳ Ξ)))
  lookup^R eq₁₂^R k = cong (injectʳ Ξ) (lookup-base^Var (lookup ρ₂ k))

  eq₁^R : ∀[ Eq^R ] (ρ₁₁ >> ρ₁₂) ρ₁₃
  eq₁^R = eq₁₁^R >>^R eq₁₂^R


  ρ′^R : ∀[ Eq^R ] (ren (freshˡ vl^Var Θ {Ξ} >> th^Env th^Var ρ₂ (freshʳ vl^Var Ξ))
                    <$> (freshˡ vl^Tm Δ  {Ξ} >> th^Env th^Tm  ρ₁ (freshʳ vl^Var Ξ)))
                  (freshˡ vl^Tm Θ {Ξ} >> th^Env th^Tm ρ₃ (freshʳ vl^Var Ξ))
  lookup^R ρ′^R k with split Ξ k
  ... | inj₁ kˡ = begin
    ren (ρ₁₁ >> ρ₁₂) (ren (pack (injectˡ Δ)) (lookup (base vl^Tm) kˡ))
      ≡⟨ cong (ren (ρ₁₁ >> ρ₁₂) ∘ ren (pack (injectˡ Δ))) (lookup-base^Tm kˡ) ⟩
    `var (lookup (ρ₁₁ >> ρ₁₂) (injectˡ Δ kˡ))
      ≡⟨ cong `var (injectˡ->> ρ₁₁ ρ₁₂ kˡ) ⟩
    `var (lookup ρ₁₁ kˡ)
      ≡⟨ cong `var (lookup^R eq₁₁^R kˡ) ⟩
    `var (injectˡ Θ kˡ)
      ≡⟨ cong (ren (pack (injectˡ Θ))) (sym (lookup-base^Tm kˡ)) ⟩
    ren (pack (injectˡ Θ)) (lookup (base vl^Tm) kˡ)
      ∎
  ... | inj₂ kʳ = begin
    ren (ρ₁₁ >> ρ₁₂) (ren ρ₂₁ (lookup ρ₁ kʳ))
      ≡⟨ Sim.sim RenExt eq₁^R (ren ρ₂₁ (lookup ρ₁ kʳ)) ⟩
    ren ρ₁₃ (ren ρ₂₁ (lookup ρ₁ kʳ))
      ≡⟨ cong (ren ρ₁₃) (Sim.sim RenExt eq₂^R  (lookup ρ₁ kʳ)) ⟩
    ren ρ₁₃ (ren (pack (injectʳ Ξ)) (lookup ρ₁ kʳ))
      ≡⟨ Fus.fus (Ren² d) eq^R (lookup ρ₁ kʳ) ⟩
    ren (select ρ₂ (pack (injectʳ Ξ))) (lookup ρ₁ kʳ)
      ≡⟨ sym (Fus.fus (Ren² d) eq₃^R (lookup ρ₁ kʳ)) ⟩
    ren ρ₃₁ (ren ρ₂ (lookup ρ₁ kʳ))
      ≡⟨ cong (ren ρ₃₁) (lookup^R ρ^R kʳ) ⟩
    ren ρ₃₁ (lookup ρ₃ kʳ)
      ∎ where

    ρ₂₁ = th^Env th^Var (base vl^Var) (pack (injectʳ Ξ))

    eq₂^R : ∀[ Eq^R ] ρ₂₁ (pack (injectʳ Ξ))
    lookup^R eq₂^R k = cong (injectʳ Ξ) (lookup-base^Var k)

    ρ₃₁ = th^Env th^Var (base vl^Var) (pack (injectʳ Ξ))

    eq₃^R : ∀[ Eq^R ] (select ρ₂ ρ₃₁) (select ρ₂ (pack (injectʳ Ξ)))
    lookup^R eq₃^R k = cong (injectʳ Ξ) (lookup-base^Var (lookup ρ₂ k))

    eq^R : ∀[ Eq^R ] (select (pack (injectʳ Ξ)) ρ₁₃) (select ρ₂ (pack (injectʳ Ξ)))
    lookup^R eq^R k with split Ξ (injectʳ Ξ k) | split-injectʳ Ξ k
    lookup^R eq^R k | .(inj₂ k) | refl = refl

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

 unLetSub : ∀ {Γ Δ Θ σ s} (t : Tm (d `+ Let) s σ Γ) {ρ₁ ρ₃} {ρ₂ : (Δ ─Env) (Tm d ∞) Θ} →
            ∀[ Eq^R ] (sub ρ₂ <$> ρ₁) ρ₃ → sub ρ₂ (unLet ρ₁ t) ≡ unLet ρ₃ t
 unLetSub-body :
   ∀ Ξ σ {Γ Δ Θ s} (t : Scope (Tm (d `+ Let) s) Ξ σ Γ) {ρ₁ ρ₃} {ρ₂ : (Δ ─Env) (Tm d ∞) Θ} →
   ∀[ Eq^R ] (sub ρ₂ <$> ρ₁) ρ₃ →
   reify vl^Tm Ξ σ (Sem.body Substitution ρ₂ Ξ σ (reify vl^Tm Ξ σ (Sem.body UnLet ρ₁ Ξ σ t)))
   ≡ reify vl^Tm Ξ σ (Sem.body UnLet ρ₃ Ξ σ t)

 unLetSub (`var v) ρ^R = lookup^R ρ^R v
 unLetSub (`con (false , (σ , τ) , e , t , refl)) {ρ₁} {ρ₃} {ρ₂} ρ^R = unLetSub t $ pack^R $ λ where
   z     → unLetSub e ρ^R
   (s v) → begin
     sub ρ₂ (ren (pack id) (lookup ρ₁ v))
       ≡⟨ cong (sub ρ₂) (ren-id′ (lookup ρ₁ v)) ⟩
     sub ρ₂ (lookup ρ₁ v)
       ≡⟨ lookup^R ρ^R v ⟩
     lookup ρ₃ v
       ≡⟨ sym (ren-id′ (lookup ρ₃ v)) ⟩
     ren (pack id) (lookup ρ₃ v)
       ∎
 unLetSub (`con (true  , r)) {ρ₁} {ρ₃} {ρ₂} ρ^R = cong `con $ begin
   fmap d (reify vl^Tm) (fmap d (Sem.body Substitution ρ₂) (fmap d (reify vl^Tm) (fmap d (Sem.body UnLet ρ₁) r)))
     ≡⟨ fmap² d (Sem.body Substitution ρ₂) (reify vl^Tm) (fmap d (reify vl^Tm) (fmap d (Sem.body UnLet ρ₁) r)) ⟩
   fmap d _ (fmap d (reify vl^Tm) (fmap d (Sem.body UnLet ρ₁) r))
     ≡⟨ fmap² d (reify vl^Tm) _ _ ⟩
   fmap d _ (fmap d (Sem.body UnLet ρ₁) r)
     ≡⟨ fmap² d (Sem.body UnLet ρ₁) _ _ ⟩
   fmap d _ r
     ≡⟨ fmap-ext d (λ Ξ i b → unLetSub-body Ξ i b ρ^R) r ⟩
   fmap d (λ Φ i → reify vl^Tm Φ i ∘ Sem.body UnLet ρ₃ Φ i) r
     ≡⟨ sym (fmap² d (Sem.body UnLet ρ₃) (reify vl^Tm) r) ⟩
   fmap d (reify vl^Tm) (fmap d (Sem.body UnLet ρ₃) r)
     ∎
 unLetSub-body [] σ t ρ^R = unLetSub t ρ^R
 unLetSub-body Ξ@(x ∷ xs) σ {Γ} {Δ} {Θ} t {ρ₁} {ρ₃} {ρ₂} ρ^R = unLetSub t ρ′^R where

  ρ₁₁ : (Ξ ─Env) (Tm d ∞) (Ξ ++ Θ)
  ρ₁₁ = th^Env th^Tm (base vl^Tm) (pack (injectˡ Θ))
  ρ₁₂ = th^Env th^Tm ρ₂ (th^Env th^Var (base vl^Var) (pack (injectʳ Ξ)))

  ρ₁₃ = pack (`var ∘ injectˡ Θ {Ξ}) >> th^Env th^Tm ρ₂ (pack (injectʳ Ξ))

  eq₁₁^R : ∀[ Eq^R ] ρ₁₁ (pack (`var ∘ injectˡ Θ))
  lookup^R eq₁₁^R k = cong (ren (pack (injectˡ Θ))) (lookup-base^Tm k)

  eq₁₂^R : ∀[ Eq^R ] ρ₁₂ (th^Env th^Tm ρ₂ (pack (injectʳ Ξ)))
  lookup^R eq₁₂^R k =
    Sim.sim RenExt (pack^R (cong (injectʳ Ξ) ∘ lookup-base^Var)) (lookup ρ₂ k)

  eq₁^R : ∀[ Eq^R ] (ρ₁₁ >> ρ₁₂) ρ₁₃
  eq₁^R = eq₁₁^R >>^R eq₁₂^R

  ρ₂₁ = th^Env th^Var (base vl^Var) (pack (injectʳ Ξ))

  ρ′^R : ∀[ Eq^R ] (sub (freshˡ vl^Tm Θ {Ξ} >> th^Env th^Tm ρ₂ (freshʳ vl^Var Ξ))
                    <$> (freshˡ vl^Tm Δ  {Ξ} >> th^Env th^Tm  ρ₁ (freshʳ vl^Var Ξ)))
                  (freshˡ vl^Tm Θ {Ξ} >> th^Env th^Tm ρ₃ (freshʳ vl^Var Ξ))
  lookup^R ρ′^R k with split Ξ k
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
      ≡⟨ Sim.sim SubExt eq₁^R (ren ρ₂₁ (lookup ρ₁ kʳ)) ⟩
    sub ρ₁₃ (ren ρ₂₁ (lookup ρ₁ kʳ))
      ≡⟨ cong (sub ρ₁₃) (Sim.sim RenExt eq₂^R  (lookup ρ₁ kʳ)) ⟩
    sub ρ₁₃ (ren (pack (injectʳ Ξ)) (lookup ρ₁ kʳ))
      ≡⟨ Fus.fus (F.RenSub d) eq^R (lookup ρ₁ kʳ) ⟩
    sub (th^Env th^Tm ρ₂ (pack (injectʳ Ξ))) (lookup ρ₁ kʳ)
      ≡⟨ sym (Fus.fus (SubRen d) eq₃^R (lookup ρ₁ kʳ)) ⟩
    ren ρ₃₁ (sub ρ₂ (lookup ρ₁ kʳ))
      ≡⟨ cong (ren ρ₃₁) (lookup^R ρ^R kʳ) ⟩
    ren ρ₃₁ (lookup ρ₃ kʳ)
      ∎ where

    eq₂^R : ∀[ Eq^R ] ρ₂₁ (pack (injectʳ Ξ))
    lookup^R eq₂^R k = cong (injectʳ Ξ) (lookup-base^Var k)

    ρ₃₁ = th^Env th^Var (base vl^Var) (pack (injectʳ Ξ))

    eq₃^R : ∀[ Eq^R ] (ren ρ₃₁ <$> ρ₂) (th^Env th^Tm ρ₂ (pack (injectʳ Ξ)))
    lookup^R eq₃^R k =
      Sim.sim RenExt (pack^R (cong (injectʳ Ξ) ∘ lookup-base^Var)) (lookup ρ₂ k)

    eq^R : ∀[ Eq^R ] (select (pack (injectʳ Ξ)) ρ₁₃) (th^Env th^Tm ρ₂ (pack (injectʳ Ξ)))
    lookup^R eq^R k with split Ξ (injectʳ Ξ k) | split-injectʳ Ξ k
    lookup^R eq^R k | .(inj₂ k) | refl = refl
\end{code}

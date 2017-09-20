\begin{code}
module Generic.Fusion where

open import Size
open import Data.Sum
open import Data.List hiding ([_] ; zip)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import indexed
open import rel
open import var hiding (_<$>_)
open import varlike
open import environment

open import Generic.Syntax
open import Generic.Semantics
open import Generic.Zip
open import Generic.Simulation using (reify^R ; VarTm^R ; vl^VarTm)

module _  {I : Set} {𝓥₁ 𝓥₂ 𝓥₃ 𝓒₁ 𝓒₂ 𝓒₃ : I → List I → Set}
          (𝓡^Env : {Γ Δ Θ : List I} → (Γ ─Env) 𝓥₁ Δ → (Δ ─Env) 𝓥₂ Θ → (Γ ─Env) 𝓥₃ Θ → Set)
          (𝓡^𝓥  : Rel 𝓥₂ 𝓥₃)
          (𝓡^𝓒   : Rel 𝓒₂ 𝓒₃)
          where

 record Fus (d : Desc I) (𝓢₁ : Sem d 𝓥₁ 𝓒₁) (𝓢₂ : Sem d 𝓥₂ 𝓒₂) (𝓢₃ : Sem d 𝓥₃ 𝓒₃) : Set where
   field  quote₁  : (i : I) → [ 𝓒₁ i ⟶ Tm d ∞ i ]
          vl^𝓥₁  : VarLike 𝓥₁
          th^R    : {Γ Δ Θ Ξ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} →
                    (σ : Thinning Θ Ξ) → 𝓡^Env ρ₁ ρ₂ ρ₃ → 𝓡^Env ρ₁ (th^Env (Sem.th^𝓥 𝓢₂) ρ₂ σ) (th^Env (Sem.th^𝓥 𝓢₃) ρ₃ σ)
          >>^R   : {Γ Δ Θ Ξ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} →
                    {ρ₄ : (Ξ ─Env) 𝓥₂ Θ} {ρ₅ : (Ξ ─Env) 𝓥₃ Θ} → 𝓡^Env ρ₁ ρ₂ ρ₃ → ∀[ 𝓡^𝓥 ] ρ₄ ρ₅ →
                    𝓡^Env (freshˡ vl^𝓥₁ Δ {Ξ} >> th^Env (Sem.th^𝓥 𝓢₁) ρ₁ (freshʳ vl^Var Ξ)) (ρ₄ >> ρ₂) (ρ₅ >> ρ₃)
          var^R   : {Γ Δ Θ : List I} {i : I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} →
                    𝓡^Env ρ₁ ρ₂ ρ₃ → (v : Var i Γ) →
                    rel 𝓡^𝓒 (Sem.sem 𝓢₂ ρ₂ (quote₁ i (Sem.var 𝓢₁ (lookup ρ₁ v)))) (Sem.var 𝓢₃ (lookup ρ₃ v))
          alg^R   : {Γ Δ : List I} {i : I} {b₁ : ⟦ d ⟧ (Kripke 𝓥₁ 𝓒₁) i Γ} {b₃ : ⟦ d ⟧ (Kripke 𝓥₃ 𝓒₃) i Δ} →
                    {ρ₂ : (Γ ─Env) 𝓥₂ Δ} →
                    Zip d (Kripke^R 𝓡^𝓥 𝓡^𝓒) (fmap d (λ Δ i → Sem.body 𝓢₂ ρ₂ Δ i ∘ quote₁ i ∘ reify vl^𝓥₁ Δ i) b₁) b₃ →
                    rel 𝓡^𝓒 (Sem.sem 𝓢₂ ρ₂ (quote₁ i (Sem.alg 𝓢₁ b₁))) (Sem.alg 𝓢₃ b₃)


   fus  : {s : Size} {i : I} {Γ Δ Θ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} →
          𝓡^Env ρ₁ ρ₂ ρ₃ → (t : Tm d s i Γ) →
          rel 𝓡^𝓒  (Sem.sem 𝓢₂ ρ₂ (quote₁ i (Sem.sem 𝓢₁ ρ₁ t)))
                     (Sem.sem 𝓢₃ ρ₃ t)
   body : {s : Size} {Γ Θ Ξ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Θ} {ρ₂ : (Θ ─Env) 𝓥₂ Ξ} {ρ₃ : (Γ ─Env) 𝓥₃ Ξ} →
          𝓡^Env ρ₁ ρ₂ ρ₃ → (Δ : List I) (i : I) (b : Scope (Tm d s) Δ i Γ) →
          Kripke^R 𝓡^𝓥 𝓡^𝓒 Δ i (Sem.body 𝓢₂ ρ₂ Δ i (quote₁ i (reify vl^𝓥₁ Δ i (Sem.body 𝓢₁ ρ₁ Δ i b))))
                                   (Sem.body 𝓢₃ ρ₃ Δ i b)

   fus ρ^R (`var v) = var^R ρ^R v
   fus ρ^R (`con t) = alg^R (rew (zip d (body ρ^R) t)) where

     eq  = fmap² d (Sem.body 𝓢₁ _) (λ Δ i t → Sem.body 𝓢₂ _ Δ i (quote₁ i (reify vl^𝓥₁ Δ i t))) t
     rew = subst (λ v → Zip d (Kripke^R 𝓡^𝓥 𝓡^𝓒) v _) (sym eq)

   body ρ^R []       i b = fus ρ^R b
   body ρ^R (σ ∷ Δ)  i b = λ ren vs^R → fus (>>^R (th^R ren ρ^R) vs^R) b


module _ {I : Set} (d : Desc I) where

 open ≡-Reasoning

 Ren² : Fus (λ ρ₁ → ∀[ Eq^R ] ∘ (select ρ₁)) Eq^R Eq^R d Renaming Renaming Renaming
 Fus.quote₁ Ren² = λ _ t → t
 Fus.vl^𝓥₁ Ren² = vl^Var
 Fus.th^R Ren² = λ σ ρ^R → pack^R (λ k → cong (lookup σ) (lookup^R ρ^R k))
 Fus.>>^R Ren² {Γ} {Δ} {Θ} {Ξ} {ρ₁} {ρ₂} {ρ₃} {ρ₄} {ρ₅} = λ ρ^R vs^R → pack^R (aux ρ^R vs^R) where

   aux : ∀[ Eq^R ] (select ρ₁ ρ₂) ρ₃ → ∀[ Eq^R ] ρ₄ ρ₅ → {i : I} (k : Var i (Ξ ++ Γ)) →
         [ lookup ρ₄ , lookup ρ₂ ]′ (split Ξ ([ lookup (freshˡ vl^Var Δ) , (lookup (freshʳ vl^Var Ξ) ∘′ (lookup ρ₁)) ]′ (split Ξ k)))
       ≡ [ lookup ρ₅ , lookup ρ₃ ]′ (split Ξ k)
   aux ρ^R vs^R k with split Ξ k
   ... | inj₁ kˡ =
     begin
       [ lookup ρ₄ , lookup ρ₂ ] (split Ξ (injectˡ Δ (lookup (base vl^Var) kˡ)))
           ≡⟨ cong [ lookup ρ₄ , lookup ρ₂ ]′ (split-injectˡ Δ (lookup (base vl^Var) kˡ)) ⟩
       lookup ρ₄ (lookup (base vl^Var) kˡ)
           ≡⟨ cong (lookup ρ₄) (lookup-base^Var kˡ) ⟩
       lookup ρ₄ kˡ
           ≡⟨ lookup^R vs^R kˡ ⟩
       lookup ρ₅ kˡ
     ∎
   ... | inj₂ kʳ =
     begin
       [ lookup ρ₄ , lookup ρ₂ ] (split Ξ (injectʳ Ξ (lookup (base vl^Var) (lookup ρ₁ kʳ))))
           ≡⟨ cong [ lookup ρ₄ , lookup ρ₂ ]′ (split-injectʳ Ξ (lookup (base vl^Var) (lookup ρ₁ kʳ))) ⟩
       lookup ρ₂ (lookup (base vl^Var) (lookup ρ₁ kʳ))
           ≡⟨ cong (lookup ρ₂) (lookup-base^Var (lookup ρ₁ kʳ)) ⟩
       lookup ρ₂ (lookup ρ₁ kʳ)
           ≡⟨ lookup^R ρ^R kʳ ⟩
       lookup ρ₃ kʳ
     ∎

 Fus.var^R Ren² = λ ρ^R v → cong `var (lookup^R ρ^R v)
 Fus.alg^R Ren² {b₁ = b₁} {b₃} {ρ} = λ zipped → cong `con $
   begin
     fmap d (reify vl^Var) (fmap d (Sem.body Renaming ρ) (fmap d (reify vl^Var) b₁))
         ≡⟨ cong (fmap d (reify vl^Var)) (fmap² d (reify vl^Var) (Sem.body Renaming ρ) b₁) ⟩
     fmap d (reify vl^Var) (fmap d (λ Φ i → (Sem.body Renaming ρ Φ i) ∘ (reify vl^Var Φ i)) b₁)
         ≡⟨ zip^reify Eq^R (reify^R Eq^R Eq^R (vl^Refl vl^Var)) d zipped ⟩
     fmap d (reify vl^Var) b₃
   ∎

 ren² : ∀ {Γ Δ Θ i} (t : Tm d ∞ i Γ) (ρ₁ : Thinning Γ Δ) (ρ₂ : Thinning Δ Θ) →
        ren ρ₂ (ren ρ₁ t) ≡ ren (select ρ₁ ρ₂) t
 ren² t ρ₁ ρ₂ = Fus.fus Ren² (pack^R (λ _ → refl)) t

 RenSub : Fus (λ ρ₁ → ∀[ Eq^R ] ∘ (select ρ₁)) Eq^R Eq^R d Renaming Substitution Substitution
 Fus.quote₁  RenSub = λ _ t → t
 Fus.vl^𝓥₁  RenSub = vl^Var
 Fus.th^R    RenSub = λ σ ρ^R → pack^R (λ k → cong (ren σ) (lookup^R ρ^R k))
 Fus.>>^R   RenSub {Γ} {Δ} {Θ} {Ξ} {ρ₁} {ρ₂} {ρ₃} {ρ₄} {ρ₅} = λ ρ^R vs^R → pack^R (aux ρ^R vs^R) where

   aux : ∀[ Eq^R ] (select ρ₁ ρ₂) ρ₃ → ∀[ Eq^R ] ρ₄ ρ₅ → {i : I} (k : Var i (Ξ ++ Γ)) →
         [ lookup ρ₄ , lookup ρ₂ ]′ (split Ξ ([ lookup (freshˡ vl^Var Δ) , (lookup (freshʳ vl^Var Ξ) ∘′ (lookup ρ₁)) ]′ (split Ξ k)))
       ≡ [ lookup ρ₅ , lookup ρ₃ ]′ (split Ξ k)
   aux ρ^R vs^R k with split Ξ k
   ... | inj₁ kˡ =
     begin
       [ lookup ρ₄ , lookup ρ₂ ] (split Ξ (injectˡ Δ (lookup (base vl^Var) kˡ)))
           ≡⟨ cong [ lookup ρ₄ , lookup ρ₂ ]′ (split-injectˡ Δ (lookup (base vl^Var) kˡ)) ⟩
       lookup ρ₄ (lookup (base vl^Var) kˡ)
           ≡⟨ cong (lookup ρ₄) (lookup-base^Var kˡ) ⟩
       lookup ρ₄ kˡ
           ≡⟨ lookup^R vs^R kˡ ⟩
       lookup ρ₅ kˡ
     ∎
   ... | inj₂ kʳ =
     begin
       [ lookup ρ₄ , lookup ρ₂ ] (split Ξ (injectʳ Ξ (lookup (base vl^Var) (lookup ρ₁ kʳ))))
           ≡⟨ cong [ lookup ρ₄ , lookup ρ₂ ]′ (split-injectʳ Ξ (lookup (base vl^Var) (lookup ρ₁ kʳ))) ⟩
       lookup ρ₂ (lookup (base vl^Var) (lookup ρ₁ kʳ))
           ≡⟨ cong (lookup ρ₂) (lookup-base^Var (lookup ρ₁ kʳ)) ⟩
       lookup ρ₂ (lookup ρ₁ kʳ)
           ≡⟨ lookup^R ρ^R kʳ ⟩
       lookup ρ₃ kʳ
     ∎

 Fus.var^R   RenSub = λ ρ^R v → lookup^R ρ^R v
 Fus.alg^R   RenSub {b₁ = b₁} {b₃} {ρ} = λ zipped → cong `con $
   begin
     fmap d (reify vl^Tm) (fmap d (Sem.body Substitution ρ) (fmap d (reify vl^Var) b₁))
         ≡⟨ cong (fmap d (reify vl^Tm)) (fmap² d (reify vl^Var) (Sem.body Substitution ρ) b₁) ⟩
     fmap d (reify vl^Tm) (fmap d (λ Φ i → (Sem.body Substitution ρ Φ i) ∘ (reify vl^Var Φ i)) b₁)
         ≡⟨ zip^reify Eq^R (reify^R Eq^R Eq^R (vl^Refl vl^Tm)) d zipped ⟩
      fmap d (reify vl^Tm) b₃
   ∎

 rensub : ∀ {Γ Δ Θ i} (t : Tm d ∞ i Γ) (ρ₁ : Thinning Γ Δ) (ρ₂ : (Δ ─Env) (Tm d ∞) Θ) →
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
 Fus.>>^R   SubRen {Γ} {Δ} {Θ} {Ξ} {ρ₁} {ρ₂} {ρ₃} {ρ₄} {ρ₅} = λ ρ^R vs^R → pack^R (aux ρ^R vs^R) where

   aux : ∀[ Eq^R ] (ren ρ₂ <$> ρ₁) ρ₃ → ∀[ VarTm^R ] ρ₄ ρ₅ → {i : I} (k : Var i (Ξ ++ Γ)) →
         ren (ρ₄ >> ρ₂) ([ (ren (pack (injectˡ Δ)) ∘ (lookup (base vl^Tm)))
                         , (ren (freshʳ vl^Var Ξ)  ∘ (lookup ρ₁))
                         ] (split Ξ k))
         ≡ [ lookup ρ₅ , lookup ρ₃ ]′ (split Ξ k)
   aux ρ^R vs^R k with split Ξ k
   ... | inj₁ kˡ =
     begin
       ren (ρ₄ >> ρ₂) (ren (pack (injectˡ Δ)) (lookup (base vl^Tm) kˡ))
            ≡⟨ Fus.fus Ren² (pack^R (injectˡ->> ρ₄ ρ₂)) (lookup (base vl^Tm) kˡ) ⟩
       ren ρ₄ (lookup (base vl^Tm) kˡ)
            ≡⟨ cong (ren ρ₄) (lookup-base^Tm kˡ) ⟩
       ren ρ₄ (`var kˡ)
            ≡⟨ lookup^R vs^R kˡ ⟩
       lookup ρ₅ kˡ
     ∎
   ... | inj₂ kʳ =
     begin
       ren (ρ₄ >> ρ₂) (ren (freshʳ vl^Var Ξ) (lookup ρ₁ kʳ))
            ≡⟨ Fus.fus Ren² (pack^R (freshʳ->> Ξ ρ₄ ρ₂)) (lookup ρ₁ kʳ) ⟩
       ren ρ₂ (lookup ρ₁ kʳ)
            ≡⟨ lookup^R ρ^R kʳ ⟩
       lookup ρ₃ kʳ
     ∎

 Fus.var^R   SubRen = λ ρ^R v → lookup^R ρ^R v
 Fus.alg^R   SubRen {b₁ = b₁} {b₃} {ρ} = λ zipped → cong `con $
   begin
     fmap d (reify vl^Var) (fmap d (Sem.body Renaming ρ) (fmap d (reify vl^Tm) b₁))
         ≡⟨ cong (fmap d (reify vl^Var)) (fmap² d (reify vl^Tm) (Sem.body Renaming ρ) b₁) ⟩
     fmap d (reify vl^Var) (fmap d (λ Φ i → (Sem.body Renaming ρ Φ i) ∘ (reify vl^Tm Φ i)) b₁)
         ≡⟨ zip^reify VarTm^R (reify^R VarTm^R Eq^R vl^VarTm) d zipped ⟩
      fmap d (reify vl^Tm) b₃
   ∎

 subren : ∀ {Γ Δ Θ i} (t : Tm d ∞ i Γ) (ρ₁ : (Γ ─Env) (Tm d ∞) Δ) (ρ₂ : Thinning Δ Θ) →
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
 Fus.>>^R Sub² {Γ} {Δ} {Θ} {Ξ} {ρ₁} {ρ₂} {ρ₃} {ρ₄} {ρ₅} = λ ρ^R vs^R → pack^R (aux ρ^R vs^R) where

   aux : ∀[ Eq^R ] (sub ρ₂ <$> ρ₁) ρ₃ → ∀[ Eq^R ] ρ₄ ρ₅ → {i : I} (k : Var i (Ξ ++ Γ)) →
         sub (ρ₄ >> ρ₂) ([ lookup (freshˡ vl^Tm Δ) , ren (freshʳ vl^Var Ξ) ∘ lookup ρ₁ ]′ (split Ξ k))
         ≡ [ lookup ρ₅ , lookup ρ₃ ]′ (split Ξ k)
   aux ρ^R vs^R k with split Ξ k
   ... | inj₁ kˡ =
     begin
       sub (ρ₄ >> ρ₂) (ren (pack (injectˡ Δ)) (lookup (base vl^Tm) kˡ))
            ≡⟨ Fus.fus RenSub (pack^R (injectˡ->> ρ₄ ρ₂)) (lookup (base vl^Tm) kˡ) ⟩
       sub ρ₄ (lookup (base vl^Tm) kˡ)
            ≡⟨ cong (sub ρ₄) (lookup-base^Tm kˡ) ⟩
       sub ρ₄ (`var kˡ)
            ≡⟨ lookup^R vs^R kˡ ⟩
       lookup ρ₅ kˡ
     ∎
   ... | inj₂ kʳ =
     begin
       sub (ρ₄ >> ρ₂) (ren (freshʳ vl^Var Ξ) (lookup ρ₁ kʳ))
            ≡⟨ Fus.fus RenSub (pack^R (freshʳ->> Ξ ρ₄ ρ₂)) (lookup ρ₁ kʳ) ⟩
       sub ρ₂ (lookup ρ₁ kʳ)
            ≡⟨ lookup^R ρ^R kʳ ⟩
       lookup ρ₃ kʳ
     ∎
 Fus.var^R Sub² = λ ρ^R v → lookup^R ρ^R v
 Fus.alg^R Sub² {b₁ = b₁} {b₃} {ρ} = λ zipped → cong `con $
   begin
     fmap d (reify vl^Tm) (fmap d (Sem.body Substitution ρ) (fmap d (reify vl^Tm) b₁))
         ≡⟨ cong (fmap d (reify vl^Tm)) (fmap² d (reify vl^Tm) (Sem.body Substitution ρ) b₁) ⟩
     fmap d (reify vl^Tm) (fmap d (λ Φ i → (Sem.body Substitution ρ Φ i) ∘ (reify vl^Tm Φ i)) b₁)
         ≡⟨ zip^reify Eq^R (reify^R Eq^R Eq^R (vl^Refl vl^Tm)) d zipped ⟩
      fmap d (reify vl^Tm) b₃
   ∎

 sub² : ∀ {Γ Δ Θ i} (t : Tm d ∞ i Γ) (ρ₁ : (Γ ─Env) (Tm d ∞) Δ) (ρ₂ : (Δ ─Env) (Tm d ∞) Θ) →
          sub ρ₂ (sub ρ₁ t) ≡ sub (sub ρ₂ <$> ρ₁) t
 sub² t ρ₁ ρ₂ = Fus.fus Sub² (pack^R (λ k → refl)) t


-- Corollary

 renβ : ∀ {Γ Δ i j} (b : Tm d ∞ j (i ∷ Γ)) (u : Tm d ∞ i Γ) (ρ : Thinning Γ Δ) →
        ren ρ (b [ u /0]) ≡ ren (lift vl^Var (i ∷ []) ρ) b [ ren ρ u /0]
 renβ {i = i} b u ρ = begin
     ren ρ (b [ u /0])         ≡⟨ subren b (u /0]) ρ ⟩
     sub (ren ρ <$> (u /0])) b ≡⟨ sym (Fus.fus RenSub eq^R b) ⟩
     ren ρ′ b [ ren ρ u /0]    ∎ where

     ρ′ = lift vl^Var (i ∷ []) ρ

     eq^R : ∀[ Eq^R ] (select ρ′ (ren ρ u /0])) (ren ρ <$> (u /0]))
     lookup^R eq^R z     = refl
     lookup^R eq^R (s k) = begin
       lookup (base vl^Tm) (lookup (base vl^Var) (lookup ρ k)) ≡⟨ lookup-base^Tm _ ⟩
       `var (lookup (base vl^Var) (lookup ρ k))                ≡⟨ cong `var (lookup-base^Var _) ⟩
       `var (lookup ρ k)                                       ≡⟨ sym (cong (ren ρ) (lookup-base^Tm k)) ⟩
       ren ρ (lookup (base vl^Tm) k)                           ∎

 subβ : ∀ {Γ Δ i j} (b : Tm d ∞ j (i ∷ Γ)) (u : Tm d ∞ i Γ) (ρ : (Γ ─Env) (Tm d ∞) Δ) →
        sub ρ (b [ u /0]) ≡ sub (lift vl^Tm (i ∷ []) ρ) b [ sub ρ u /0]
 subβ {i = i} b u ρ = begin
   sub ρ (b [ u /0])                  ≡⟨ sub² b (u /0]) ρ ⟩
   sub (sub ρ <$> (base vl^Tm ∙ u)) b ≡⟨ sym (Fus.fus Sub² eq^R′ b) ⟩
   sub ρ′ b [ sub ρ u /0]             ∎ where

   ρ′ = lift vl^Tm (i ∷ []) ρ
   σ  = freshʳ vl^Var (i ∷ [])

   eq^R : ∀[ Eq^R ] (select σ (sub ρ u /0])) (base vl^Tm)
   lookup^R eq^R z     = refl
   lookup^R eq^R (s k) = cong (ren extend ∘ lookup (base vl^Tm)) (lookup-base^Var k)

   eq^R′ : ∀[ Eq^R ] (sub (sub ρ u /0]) <$> ρ′) (sub ρ <$> (base vl^Tm ∙ u))
   lookup^R eq^R′ z     = refl
   lookup^R eq^R′ (s k) = begin
     sub (sub ρ u /0]) (ren σ (lookup ρ k))  ≡⟨ Fus.fus RenSub eq^R (lookup ρ k) ⟩
     sub (base vl^Tm) (lookup ρ k)           ≡⟨ {!!} ⟩ -- need sub-id
     lookup ρ k                              ≡⟨ cong (sub ρ) (sym $ lookup-base^Tm k) ⟩
     sub ρ (lookup (base vl^Tm) k) ∎

\end{code}

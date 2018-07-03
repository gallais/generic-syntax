module Generic.Fusion where

open import Size
open import Data.Sum
open import Data.List hiding ([_] ; zip ; lookup)
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

module _  {I : Set} {𝓥₁ 𝓥₂ 𝓥₃ 𝓒₁ 𝓒₂ 𝓒₃ : I → List I → Set}
          (𝓡^E : {Γ Δ Θ : List I} → (Γ ─Env) 𝓥₁ Δ → (Δ ─Env) 𝓥₂ Θ → (Γ ─Env) 𝓥₃ Θ → Set)
          (𝓡^𝓥  : Rel 𝓥₂ 𝓥₃)
          (𝓡^𝓒   : Rel 𝓒₂ 𝓒₃)
          where

 record Fus (d : Desc I) (𝓢₁ : Sem d 𝓥₁ 𝓒₁) (𝓢₂ : Sem d 𝓥₂ 𝓒₂) (𝓢₃ : Sem d 𝓥₃ 𝓒₃) : Set where
   field

     quote₁  :  (i : I) → [ 𝓒₁ i ⟶ Tm d ∞ i ]

     vl^𝓥₁   :  VarLike 𝓥₁

     th^R    :  {Γ Δ Θ Ξ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} → (σ : Thinning Θ Ξ) → 𝓡^E ρ₁ ρ₂ ρ₃ →
                𝓡^E ρ₁ (th^Env (Sem.th^𝓥 𝓢₂) ρ₂ σ) (th^Env (Sem.th^𝓥 𝓢₃) ρ₃ σ)

     >>^R    :  {Γ Δ Θ Ξ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} {ρ₄ : (Ξ ─Env) 𝓥₂ Θ} {ρ₅ : (Ξ ─Env) 𝓥₃ Θ} → 𝓡^E ρ₁ ρ₂ ρ₃ → ∀[ 𝓡^𝓥 ] ρ₄ ρ₅ →
                𝓡^E (freshˡ vl^𝓥₁ Δ {Ξ} >> th^Env (Sem.th^𝓥 𝓢₁) ρ₁ (freshʳ vl^Var Ξ)) (ρ₄ >> ρ₂) (ρ₅ >> ρ₃)

     var^R   :  {Γ Δ Θ : List I} {i : I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} → 𝓡^E ρ₁ ρ₂ ρ₃ → (v : Var i Γ) →
                rel 𝓡^𝓒  (Sem.sem 𝓢₂ ρ₂ (quote₁ i (Sem.var 𝓢₁ (lookup ρ₁ v))))
                           (Sem.var 𝓢₃ (lookup ρ₃ v))

     alg^R   :  {Γ Δ Θ : List I} {s : Size} {i : I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} → (b : ⟦ d ⟧ (Scope (Tm d s)) i Γ) → 𝓡^E ρ₁ ρ₂ ρ₃ →
                let  v₁ = fmap d (Sem.body 𝓢₁ ρ₁) b
                     v₃ = fmap d (Sem.body 𝓢₃ ρ₃) b
                in Zip d (Kripke^R 𝓡^𝓥 𝓡^𝓒)
                    (fmap d (λ Δ i → Sem.body 𝓢₂ ρ₂ Δ i ∘ quote₁ i ∘ reify vl^𝓥₁ Δ i) v₁)
                    v₃ →
                rel 𝓡^𝓒 (Sem.sem 𝓢₂ ρ₂ (quote₁ i (Sem.alg 𝓢₁ v₁))) (Sem.alg 𝓢₃ v₃)



   fus  :  {s : Size} {i : I} {Γ Δ Θ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} → 𝓡^E ρ₁ ρ₂ ρ₃ → (t : Tm d s i Γ) → rel 𝓡^𝓒  (Sem.sem 𝓢₂ ρ₂ (quote₁ i (Sem.sem 𝓢₁ ρ₁ t)))
                                                                                                                                                           (Sem.sem 𝓢₃ ρ₃ t)
   body :  {s : Size} {Γ Θ Ξ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Θ} {ρ₂ : (Θ ─Env) 𝓥₂ Ξ} {ρ₃ : (Γ ─Env) 𝓥₃ Ξ} → 𝓡^E ρ₁ ρ₂ ρ₃ → (Δ : List I) (i : I) (b : Scope (Tm d s) Δ i Γ) →
           Kripke^R 𝓡^𝓥 𝓡^𝓒 Δ i   (Sem.body 𝓢₂ ρ₂ Δ i (quote₁ i (reify vl^𝓥₁ Δ i (Sem.body 𝓢₁ ρ₁ Δ i b))))
                                  (Sem.body 𝓢₃ ρ₃ Δ i b)


   fus ρ^R (`var v) = var^R ρ^R v
   fus ρ^R (`con t) = alg^R t ρ^R (rew (zip d (body ρ^R) t)) where

     eq  = fmap² d (Sem.body 𝓢₁ _) (λ Δ i t → Sem.body 𝓢₂ _ Δ i (quote₁ i (reify vl^𝓥₁ Δ i t))) t
     rew = subst (λ v → Zip d (Kripke^R 𝓡^𝓥 𝓡^𝓒) v _) (sym eq)

   body ρ^R []       i b = fus ρ^R b
   body ρ^R (σ ∷ Δ)  i b = λ ren vs^R → fus (>>^R (th^R ren ρ^R) vs^R) b


module _ {I : Set} {T : I ─Scoped} where

  open ≡-Reasoning

  -- this is the shape of environment one obtains when pushing an evaluation environment
  -- on top of a thinning into the body of a binder

  thBodyEnv :
    ∀ {Γ Δ Θ Ξ : List I} {ρ₁ : Thinning Γ Δ} {ρ₂ : (Δ ─Env) T Θ}
    {ρ₃ : (Γ ─Env) T Θ} {ρ₄ ρ₅ : (Ξ ─Env) T Θ}
    (ρ^R : ∀[ Eq^R ] (select ρ₁ ρ₂) ρ₃) (vs^R : ∀[ Eq^R ] ρ₄ ρ₅) →
    let σ : (Ξ ++ Γ ─Env) Var (Ξ ++ Δ)
        σ = freshˡ vl^Var Δ {Ξ} >> th^Env th^Var ρ₁ (freshʳ vl^Var Ξ)
    in ∀[ Eq^R ] (select σ (ρ₄ >> ρ₂)) (ρ₅ >> ρ₃)
  lookup^R (thBodyEnv {Γ} {Δ} {Θ} {Ξ} {ρ₁} {ρ₂} {ρ₃} {ρ₄} {ρ₅} ρ^R vs^R) k
    with split Ξ k
  ... | inj₁ kˡ = begin
    lookup (ρ₄ >> ρ₂) (injectˡ Δ (lookup (base vl^Var) kˡ))
      ≡⟨ injectˡ->> ρ₄ ρ₂ (lookup (base vl^Var) kˡ) ⟩
    lookup ρ₄ (lookup (base vl^Var) kˡ)
      ≡⟨ cong (lookup ρ₄) (lookup-base^Var kˡ) ⟩
    lookup ρ₄ kˡ
      ≡⟨ lookup^R vs^R kˡ ⟩
    lookup ρ₅ kˡ
      ∎
  ... | inj₂ kʳ = begin
    lookup (ρ₄ >> ρ₂) (injectʳ Ξ (lookup (base vl^Var) (lookup ρ₁ kʳ)))
      ≡⟨ injectʳ->> ρ₄ ρ₂ (lookup (base vl^Var) (lookup ρ₁ kʳ)) ⟩
    lookup ρ₂ (lookup (base vl^Var) (lookup ρ₁ kʳ))
      ≡⟨ cong (lookup ρ₂) (lookup-base^Var (lookup ρ₁ kʳ)) ⟩
    lookup ρ₂ (lookup ρ₁ kʳ)
      ≡⟨ lookup^R ρ^R kʳ ⟩
    lookup ρ₃ kʳ
      ∎

module _ {I : Set} {d : Desc I}  {𝓥 𝓒 : I ─Scoped}
         (𝓢 : Sem d 𝓥 𝓒)
         (𝓕 : Fus (λ ρ₁ ρ₂ → ∀[ Eq^R ] (select ρ₁ ρ₂)) Eq^R Eq^R d Renaming 𝓢 𝓢)
         (eq^quote : ∀ σ {Γ} t → Fus.quote₁ 𝓕 σ {Γ} t ≡ t) where

  open ≡-Reasoning

  SemVarTm^R : Rel 𝓥 𝓒
  rel SemVarTm^R v c = Sem.var 𝓢 v ≡ c

  -- this is the shape of environment one obtains when pushing an evaluation environment
  -- on top of a substitution into the body of a binder

  subBodyEnv :
    ∀ {Γ Δ Θ Ξ} (ρ₁ : (Γ ─Env) (Tm d _) Δ) {ρ₂ : (Δ ─Env) 𝓥 Θ} {ρ₃}
    {ρ₄ : (Ξ ─Env) 𝓥 Θ} {ρ₅ : (Ξ ─Env) 𝓒 Θ} →
    ∀[ Eq^R ] (Sem.sem 𝓢 ρ₂ <$> ρ₁) ρ₃ →
    ∀[ SemVarTm^R ] ρ₄ ρ₅ →
    let σ : ((Ξ ++ Γ) ─Env) (Tm d _) (Ξ ++ Δ)
        σ = freshˡ vl^Tm Δ {Ξ} >> th^Env th^Tm ρ₁ (freshʳ vl^Var Ξ)
    in ∀[ Eq^R ] (Sem.sem 𝓢 (ρ₄ >> ρ₂) <$> σ) (ρ₅ >> ρ₃)
  lookup^R (subBodyEnv {Γ} {Δ} {Θ} {Ξ} ρ₁ {ρ₂} {ρ₃} {ρ₄} {ρ₅} ρ^R vs^R) k
    with split Ξ k
  ... | inj₁ kˡ = begin
    let t = ren (pack (injectˡ Δ)) (lookup (base vl^Tm) kˡ) in
    Sem.sem 𝓢 (ρ₄ >> ρ₂) t
      ≡⟨ cong (Sem.sem 𝓢 (ρ₄ >> ρ₂)) (sym (eq^quote _ t)) ⟩
    Sem.sem 𝓢 (ρ₄ >> ρ₂) (Fus.quote₁ 𝓕 _ t)
      ≡⟨ Fus.fus 𝓕 (pack^R (injectˡ->> ρ₄ ρ₂)) (lookup (base vl^Tm) kˡ) ⟩
    Sem.sem 𝓢 ρ₄ (lookup (base vl^Tm) kˡ)
      ≡⟨ cong (Sem.sem 𝓢 ρ₄) (lookup-base^Tm kˡ) ⟩
    Sem.var 𝓢 (lookup ρ₄ kˡ)
      ≡⟨ lookup^R vs^R kˡ ⟩
    lookup ρ₅ kˡ
      ∎
  ... | inj₂ kʳ = begin
    let t = ren (freshʳ vl^Var Ξ) (lookup ρ₁ kʳ) in
    Sem.sem 𝓢 (ρ₄ >> ρ₂) t
      ≡⟨ cong (Sem.sem 𝓢 (ρ₄ >> ρ₂)) (sym (eq^quote _ t)) ⟩
    Sem.sem 𝓢 (ρ₄ >> ρ₂) (Fus.quote₁ 𝓕 _ t)
      ≡⟨ Fus.fus 𝓕 eq^R (lookup ρ₁ kʳ) ⟩
    Sem.sem 𝓢 ρ₂ (lookup ρ₁ kʳ)
      ≡⟨ lookup^R ρ^R kʳ ⟩
    lookup ρ₃ kʳ
      ∎ where

    eq^R : ∀[ Eq^R ] (select (freshʳ vl^Var Ξ) (ρ₄ >> ρ₂)) ρ₂
    lookup^R eq^R v = begin
      lookup (select (freshʳ vl^Var Ξ) (ρ₄ >> ρ₂)) v
        ≡⟨ injectʳ->> ρ₄ ρ₂ (lookup (base vl^Var) v) ⟩
      lookup ρ₂ (lookup (base vl^Var) v)
        ≡⟨ cong (lookup ρ₂) (lookup-base^Var v) ⟩
      lookup ρ₂ v
        ∎

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
open import Generic.Simulation using (reify^R ; vl^VarTm ; Sim ; SubExt)
open import Generic.Identity

module _  {I : Set} {𝓥₁ 𝓥₂ 𝓥₃ 𝓒₁ 𝓒₂ 𝓒₃ : I → List I → Set}
          (𝓡^E : {Γ Δ Θ : List I} → (Γ ─Env) 𝓥₁ Δ → (Δ ─Env) 𝓥₂ Θ → (Γ ─Env) 𝓥₃ Θ → Set)
          (𝓡^𝓥  : Rel 𝓥₂ 𝓥₃)
          (𝓡^𝓒   : Rel 𝓒₂ 𝓒₃)
          where
\end{code}
%<*fusion>
%<*fusiontype>
\begin{code}
 record Fus (d : Desc I) (𝓢₁ : Sem d 𝓥₁ 𝓒₁) (𝓢₂ : Sem d 𝓥₂ 𝓒₂) (𝓢₃ : Sem d 𝓥₃ 𝓒₃) : Set where
   field
\end{code}
%</fusiontype>
%<*fusionquote>
\begin{code}
     quote₁  :  (i : I) → [ 𝓒₁ i ⟶ Tm d ∞ i ]
\end{code}
%</fusionquote>
%<*fusionvarlike>
\begin{code}
     vl^𝓥₁   :  VarLike 𝓥₁
\end{code}
%</fusionvarlike>
%<*fusionthinnable>
\begin{code}
     th^R    :  {Γ Δ Θ Ξ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} → (σ : Thinning Θ Ξ) → 𝓡^E ρ₁ ρ₂ ρ₃ →
                𝓡^E ρ₁ (th^Env (Sem.th^𝓥 𝓢₂) ρ₂ σ) (th^Env (Sem.th^𝓥 𝓢₃) ρ₃ σ)
\end{code}
%</fusionthinnable>
%<*fusionappend>
\begin{code}
     >>^R    :  {Γ Δ Θ Ξ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} {ρ₄ : (Ξ ─Env) 𝓥₂ Θ} {ρ₅ : (Ξ ─Env) 𝓥₃ Θ} → 𝓡^E ρ₁ ρ₂ ρ₃ → ∀[ 𝓡^𝓥 ] ρ₄ ρ₅ →
                𝓡^E (freshˡ vl^𝓥₁ Δ {Ξ} >> th^Env (Sem.th^𝓥 𝓢₁) ρ₁ (freshʳ vl^Var Ξ)) (ρ₄ >> ρ₂) (ρ₅ >> ρ₃)
\end{code}
%</fusionappend>
%<*fusionvar>
\begin{code}
     var^R   :  {Γ Δ Θ : List I} {i : I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} → 𝓡^E ρ₁ ρ₂ ρ₃ → (v : Var i Γ) →
                rel 𝓡^𝓒  (Sem.sem 𝓢₂ ρ₂ (quote₁ i (Sem.var 𝓢₁ (lookup ρ₁ v))))
                           (Sem.var 𝓢₃ (lookup ρ₃ v))
\end{code}
%</fusionvar>
%<*fusionalg>
\begin{code}
     alg^R   :  {Γ Δ Θ : List I} {s : Size} {i : I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} → (b : ⟦ d ⟧ (Scope (Tm d s)) i Γ) → 𝓡^E ρ₁ ρ₂ ρ₃ →
                let  v₁ = fmap d (Sem.body 𝓢₁ ρ₁) b
                     v₃ = fmap d (Sem.body 𝓢₃ ρ₃) b
                in Zip d (Kripke^R 𝓡^𝓥 𝓡^𝓒)
                    (fmap d (λ Δ i → Sem.body 𝓢₂ ρ₂ Δ i ∘ quote₁ i ∘ reify vl^𝓥₁ Δ i) v₁)
                    v₃ →
                rel 𝓡^𝓒 (Sem.sem 𝓢₂ ρ₂ (quote₁ i (Sem.alg 𝓢₁ v₁))) (Sem.alg 𝓢₃ v₃)
\end{code}
%</fusionalg>
%</fusion>
\begin{code}
\end{code}
%<*fusbody>
\begin{code}

   fus  :  {s : Size} {i : I} {Γ Δ Θ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} → 𝓡^E ρ₁ ρ₂ ρ₃ → (t : Tm d s i Γ) → rel 𝓡^𝓒  (Sem.sem 𝓢₂ ρ₂ (quote₁ i (Sem.sem 𝓢₁ ρ₁ t)))
                                                                                                                                                           (Sem.sem 𝓢₃ ρ₃ t)
   body :  {s : Size} {Γ Θ Ξ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Θ} {ρ₂ : (Θ ─Env) 𝓥₂ Ξ} {ρ₃ : (Γ ─Env) 𝓥₃ Ξ} → 𝓡^E ρ₁ ρ₂ ρ₃ → (Δ : List I) (i : I) (b : Scope (Tm d s) Δ i Γ) →
           Kripke^R 𝓡^𝓥 𝓡^𝓒 Δ i   (Sem.body 𝓢₂ ρ₂ Δ i (quote₁ i (reify vl^𝓥₁ Δ i (Sem.body 𝓢₁ ρ₁ Δ i b))))
                                  (Sem.body 𝓢₃ ρ₃ Δ i b)
\end{code}
%</fusbody>
\begin{code}

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

module _ {I : Set} (d : Desc I) where

 open ≡-Reasoning

 Ren² : Fus (λ ρ₁ → ∀[ Eq^R ] ∘ (select ρ₁)) Eq^R Eq^R d Renaming Renaming Renaming
 Fus.quote₁ Ren² = λ _ t → t
 Fus.vl^𝓥₁ Ren² = vl^Var
 Fus.th^R Ren² = λ σ ρ^R → pack^R (cong (lookup σ) ∘ (lookup^R ρ^R))
 Fus.>>^R Ren² = λ ρ^R vs^R → thBodyEnv ρ^R vs^R
 Fus.var^R Ren² = λ ρ^R v → cong `var (lookup^R ρ^R v)
 Fus.alg^R Ren² {ρ₁ = ρ₁} {ρ₂} {ρ₃} b ρ^R = λ zipped → cong `con $
   let v₁ = fmap d (Sem.body Renaming ρ₁) b
       v₃ = fmap d (Sem.body Renaming ρ₃) b in
   begin
     fmap d (reify vl^Var) (fmap d (Sem.body Renaming ρ₂) (fmap d (reify vl^Var) v₁))
         ≡⟨ cong (fmap d (reify vl^Var)) (fmap² d (reify vl^Var) (Sem.body Renaming ρ₂) v₁) ⟩
     fmap d (reify vl^Var) (fmap d (λ Φ i → (Sem.body Renaming ρ₂ Φ i) ∘ (reify vl^Var Φ i)) v₁)
         ≡⟨ zip^reify Eq^R (reify^R Eq^R Eq^R (vl^Refl vl^Var)) d zipped ⟩
     fmap d (reify vl^Var) v₃
   ∎
\end{code}
%<*renren>
\begin{code}
 ren² : {Γ Δ Θ : List I} {i : I} {s : Size} → (t : Tm d s i Γ) (ρ₁ : Thinning Γ Δ) (ρ₂ : Thinning Δ Θ) →
        ren ρ₂ (ren ρ₁ t) ≡ ren (select ρ₁ ρ₂) t
 ren² t ρ₁ ρ₂ = Fus.fus Ren² (pack^R (λ _ → refl)) t
\end{code}
%</renren>
\begin{code}
 RenSub : Fus (λ ρ₁ → ∀[ Eq^R ] ∘ (select ρ₁)) Eq^R Eq^R d Renaming Substitution Substitution
 Fus.quote₁  RenSub = λ _ t → t
 Fus.vl^𝓥₁  RenSub = vl^Var
 Fus.th^R    RenSub = λ σ ρ^R → pack^R (cong (ren σ) ∘ (lookup^R ρ^R))
 Fus.>>^R   RenSub = λ ρ^R vs^R → thBodyEnv ρ^R vs^R
 Fus.var^R   RenSub = λ ρ^R v → lookup^R ρ^R v
 Fus.alg^R   RenSub {ρ₁ = ρ₁} {ρ₂} {ρ₃} b ρ^R = λ zipped → cong `con $
   let v₁ = fmap d (Sem.body Renaming ρ₁) b
       v₃ = fmap d (Sem.body Substitution ρ₃) b in
   begin
     fmap d (reify vl^Tm) (fmap d (Sem.body Substitution ρ₂) (fmap d (reify vl^Var) v₁))
         ≡⟨ cong (fmap d (reify vl^Tm)) (fmap² d (reify vl^Var) (Sem.body Substitution ρ₂) v₁) ⟩
     fmap d (reify vl^Tm) (fmap d (λ Φ i → (Sem.body Substitution ρ₂ Φ i) ∘ (reify vl^Var Φ i)) v₁)
         ≡⟨ zip^reify Eq^R (reify^R Eq^R Eq^R (vl^Refl vl^Tm)) d zipped ⟩
      fmap d (reify vl^Tm) v₃
   ∎
\end{code}
%<*rensub>
\begin{code}
 rensub :  {Γ Δ Θ : List I} {i : I} {s : Size} → (t : Tm d s i Γ) (ρ₁ : Thinning Γ Δ) (ρ₂ : (Δ ─Env) (Tm d ∞) Θ) →
           sub ρ₂ (ren ρ₁ t) ≡ sub (select ρ₁ ρ₂) t
 rensub t ρ₁ ρ₂ = Fus.fus RenSub (pack^R (λ _ → refl)) t
\end{code}
%</rensub>
\begin{code}

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
\end{code}
%<*subren>
\begin{code}
 subren :  {Γ Δ Θ : List I} {i : I} {s : Size} → ∀ (t : Tm d s i Γ) (ρ₁ : (Γ ─Env) (Tm d ∞) Δ) (ρ₂ : Thinning Δ Θ) →
           ren ρ₂ (sub ρ₁ t) ≡ sub (ren ρ₂ <$> ρ₁) t
 subren t ρ₁ ρ₂ = Fus.fus SubRen (pack^R (λ k → refl)) t
\end{code}
%</subren>
\begin{code}

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
\end{code}
%<*subsub>
\begin{code}
 sub² :  {Γ Δ Θ : List I} {i : I} {s : Size} → ∀ (t : Tm d s i Γ) (ρ₁ : (Γ ─Env) (Tm d ∞) Δ) (ρ₂ : (Δ ─Env) (Tm d ∞) Θ) →
         sub ρ₂ (sub ρ₁ t) ≡ sub (sub ρ₂ <$> ρ₁) t
 sub² t ρ₁ ρ₂ = Fus.fus Sub² (pack^R (λ k → refl)) t
\end{code}
%<*subsub>
\begin{code}



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
     ≡⟨ Sim.sim SubExt (pack^R (λ v → cong (lookup (base vl^Tm)) (lookup-base^Var v))) (lookup ρ k₂) ⟩
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

\end{code}

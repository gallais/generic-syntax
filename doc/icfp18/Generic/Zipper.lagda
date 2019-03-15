\begin{code}
module Generic.Zipper where

open import Size
open import Data.Empty
open import Data.Product as P hiding (,_)
open import Data.Bool
open import Data.Sum
open import Data.List.Base as List
open import Data.List.Properties
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import var
open import indexed
open import Generic.Syntax

data Hole (I : Set) : Set where
  Here Skip : Hole I
  Deep : I → (List I → List I) → Hole I

module _ {I : Set} where

 hole : Desc I → I → (List I → List I) → Desc (I ⊎ (I × I × (List I → List I)))
 hole (`σ A d)   h δ = `σ A (λ a → hole (d a) h δ)
 hole (`X Δ j d) h δ = `X (List.map inj₁ Δ) (inj₁ j) (hole d h δ)
 hole (`∎ i)     h δ = `∎ (inj₂ (i , h , δ))

 ∂ : Desc I → Desc (I ⊎ (I × (I × (List I → List I))))
 ∂ (`σ A d)   = `σ A (λ a → ∂ (d a))
 ∂ (`X Δ j d) = `σ (Hole I) λ
                   { Here       → hole d j (Δ ++_)
                   ; (Deep i δ) → `X (List.map inj₁ Δ) (inj₂ (j , i , δ)) (hole d i (δ ∘ (Δ ++_)))
                   ; Skip       → `X (List.map inj₁ Δ) (inj₁ j) (∂ d)
                   }
 ∂ (`∎ i)     = `σ ⊥ ⊥-elim

 unHole₁ : ∀ (d : Desc I) X {h δ i Γ} →
          ⟦ hole d h δ ⟧ X (inj₁ i) (List.map inj₁ Γ) →
          ⊥
 unHole₁ (`σ A d)   X (a , v) = unHole₁ (d a) X v
 unHole₁ (`X Δ j d) X (r , v) = unHole₁ d X v
 unHole₁ (`∎ i)     X ()

 cast : ∀ (d : Desc I) {i s Γ} → Tm (∂ d) s (inj₁ i) (List.map inj₁ Γ) → Tm d s i Γ
 castD : ∀ (d : Desc I) {e i s Γ} → ⟦ ∂ d ⟧ (Scope (Tm (∂ e) s)) (inj₁ i) (List.map inj₁ Γ) → ⟦ d ⟧ (Scope (Tm e s)) i Γ

 cast d (`var k) = `var (Injective-inj₁ <$>⁻¹ k)
 cast d (`con t) = `con (castD d t)

 castD (`σ A d)       (a     , v)         = a , castD (d a) v
 castD (`∎ i)         (f     , _)         = ⊥-elim f
 castD (`X Δ j d) {e} (Here     , v)      = ⊥-elim (unHole₁ d (Scope (Tm (∂ e) _)) v)
 castD (`X Δ j d) {e} (Deep i δ , t , v ) = ⊥-elim (unHole₁ d (Scope (Tm (∂ e) _)) v)
 castD (`X Δ j d) {e} (Skip     , t , v)  = cast _ t′ , castD d v where
   t′ = subst (Tm _ _ _) (sym (map-++-commute inj₁ Δ _)) t

 unHole₂ : ∀ (d : Desc I) {s} e h δ {i j f Γ} →
          ⟦ hole d h δ ⟧ (Scope (Tm (∂ e) s)) (inj₂ (i , j , f)) (List.map inj₁ Γ) →
          ⟦ d ⟧ (Scope (Tm e s)) i Γ × j ≡ h × f ≡ δ
 unHole₂ (`σ A d)   e h δ (a , v) = P.map (a ,_) id (unHole₂ (d a) e h δ v)
 unHole₂ (`X Δ j d) e h δ (r , v) = P.map (cast _ r′ ,_) id (unHole₂ d e h δ v)
   where r′ = subst (Tm _ _ _) (sym (map-++-commute inj₁ Δ _)) r
 unHole₂ (`∎ i)     e h δ refl    = refl , refl , refl

 plug : ∀ (d : Desc I) {i s j Γ f} →
        Tm (∂ d) s (inj₂ (i , j , f)) (List.map inj₁ Γ) →
        Tm d ∞ j (f Γ) →
        Tm d ∞ i Γ
 plugD : ∀ (d : Desc I) e {i s j Γ f} →
         ⟦ ∂ d ⟧ (Scope (Tm (∂ e) s)) (inj₂ (i , j , f)) (List.map inj₁ Γ) →
         Tm e ∞ j (f Γ) →
         ⟦ d ⟧ (Scope (Tm e ∞)) i Γ

 plug d (`var k) t = ⊥-elim (impossible _ refl refl k) where

  impossible : ∀ {i′ i Γ′} Γ → i′ ≡ inj₂ i → Γ′ ≡ List.map inj₁ Γ → Var i′ Γ′ → ⊥
  impossible []      eqi ()   z
  impossible (_ ∷ _) ()  refl z
  impossible []      eqi ()   (s k)
  impossible (_ ∷ _) eqi refl (s k) = impossible _ eqi refl k

 plug d (`con v) t = `con (plugD d d v t)

 plugD (`σ A d)   e (a     , v)       t = a , plugD (d a) e v t
 plugD (`X Δ j d) e (Skip , (r , v)) t = cast _ r′ , plugD d e v t
   where r′ = subst (Tm _ _ _) (sym (map-++-commute inj₁ Δ _)) r
 plugD (`X Δ j d) e (Here  , v)       t =
   let (b , eqi , eqf) = unHole₂ d e j (Δ ++_) v
       t′ = subst₂ (Tm _ _) eqi (cong (λ f → f _) eqf) t
   in t′ , b
 plugD (`X Δ j d) e (Deep i δ , r , v) t =
   let (b , eqi , eqf) = unHole₂ d e i (δ ∘ (Δ ++_)) v
       t′ = subst₂ (Tm e _) eqi (cong (λ f → f _) eqf) t
       r′ = subst (Tm _ _ _) (sym (map-++-commute inj₁ Δ _)) r
   in plug e r′ t′ , b
 plugD (`∎ i)     e (v     , _)       t = ⊥-elim v
\end{code}

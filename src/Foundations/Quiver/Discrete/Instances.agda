{-# OPTIONS --safe #-}
module Foundations.Quiver.Discrete.Instances where

open import Foundations.Path.Base
  renaming ( refl to reflₚ
           ; sym  to symₚ )
open import Foundations.Path.Coe
open import Foundations.Path.Transport
open import Foundations.Path.Properties
open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete.Base
open import Foundations.Quiver.Fibration.Contravariant
open import Foundations.Quiver.Fibration.Covariant
open import Foundations.Quiver.Lens.Extend.Base
open import Foundations.Quiver.Lens.Pull.Assoc
open import Foundations.Quiver.Lens.Pull.Base
open import Foundations.Quiver.Lens.Pull.Universal.Pullback
open import Foundations.Quiver.Lens.Push.Assoc
open import Foundations.Quiver.Lens.Push.Base
open import Foundations.Quiver.Lens.Push.Universal.Pushforward

open import Notation.Refl
open import Notation.Sym

module _ {ℓa} {A : Type ℓa} where instance
  Path-Push : {x : A} → HPush (Disc A) 0 λ y → Disc (x ＝ y)
  Path-Push ._▷_ = _∙_
  Path-Push .push-refl {u} = id-o u

  Path-Pull : {y : A} → HPull (Disc A) 0 λ x → Disc (x ＝ y)
  Path-Pull ._◁_ = _∙_
  Path-Pull .pull-refl {v} = id-i v

  Path-RAssoc : {x : A} → RAssoc (Path-Push {x = x}) Path-Push
  Path-RAssoc .RAssoc.assoc-r = assoc

  Path-LAssoc : {y : A} → LAssoc (Path-Pull {y = y}) Path-Pull
  Path-LAssoc .assoc-l v p q = assoc p q v

  Path-Pushforwards : {x : A} → Pushforwards (Path-Push {x = x})
  Path-Pushforwards {x} .push-univ {x = y} {y = z} p q (r , s) (t , u)
    =  sym s ∙ u
    ,ₚ to-pathᴾ (subst-path-right s _ ∙ assoc s _ _ ∙ ap (_∙ u) (path-inv (sym s)) ∙ id-i u)

  Path-Pullbacks : {y : A} → Pullbacks (Path-Pull {y = y})
  Path-Pullbacks {y} .pull-univ {x} {y = z} p q (r , s) (t , u)
    =  s ∙ sym u
    ,ₚ to-pathᴾ ( subst-path-left s _ ∙ ap (_∙ s) (sym-∙ s _) ∙ sym (assoc u _ s)
                ∙ ap (u ∙_) (path-inv s) ∙ sym (id-o u))

{-# OVERLAPPING
  Path-Push Path-Pull
  Path-RAssoc Path-LAssoc
  Path-Pushforwards Path-Pullbacks
#-}


-- these are bad, use as a last resort

module Default-Extend {ℓa} {A : Type ℓa} {k ℓ-obᶠ ℓ-homᶠ}
  {F : {x y : A} → x ＝ y → ob-sig ℓ-obᶠ}
  (α : {x y : A} (p : x ＝ y) → HQuiver-onω k (F p) ℓ-homᶠ)
  ⦃ _ : ∀{x y} {p : x ＝ y} → Refl (α p) ⦄ where instance
  private module α x y p = Quiver-onω (α {x} {y} p) renaming (Het to Hom)

  Disc-Extend : Extend (Disc A) k α
  Disc-Extend .extend-l p = coe0→1 λ i → F (λ j → p (i ∧ j)) _
  Disc-Extend .extend-r p = coe1→0 λ i → F (λ j → p (i ∨ j)) _
  Disc-Extend .extend-refl = refl
  Disc-Extend .extend-coh {u} = coe0→1 (λ i → α.Hom _ _ _ (coe0→i _ i u) u) refl
  {-# INCOHERENT Disc-Extend #-}

module _ {ℓa} {A : Type ℓa} {k ℓ-obᶠ ℓ-homᶠ}
  {F : A → ob-sig ℓ-obᶠ}
  (α : (t : A) → HQuiver-onω k (F t) ℓ-homᶠ)
  ⦃ _ : ∀{t} → Refl (α t) ⦄ where
  private module α t = Quiver-onω (α t) renaming (Het to Hom)

  module Default-Push where instance
    Disc-Push : HPush (Disc A) k α
    Disc-Push ._▷_ {lfs} u p = coe0→1 (λ i → F (p i) lfs) u
    Disc-Push .push-refl {u} = coe0→1 (λ i → α.Hom _ u (coe0→i _ i u)) refl

    Disc-RAssoc : RAssoc Disc-Push Path-Push
    Disc-RAssoc .assoc-r {z} u p q = subst (λ φ → α.Hom z (u ▷ (p ▷ q)) φ)
      (subst-comp (λ ψ → F ψ _) p q u) refl

    -- TODO
    -- Disc-Pushforwards : Pushforwards (Disc A) α
    -- Disc-Pushforwards .Pushforwards.hp = Disc-Push
    -- Disc-Pushforwards .push-univ p u (v₁ , q₁) (v₂ , q₂) = {!!} ,ₚ {!!}

    {-# INCOHERENT Disc-Push Disc-RAssoc #-}

  module Default-Pull where instance
    Disc-Pull : HPull (Disc A) k α
    Disc-Pull ._◁_ p = coe1→0 (λ i → F (p i) _)
    Disc-Pull .pull-refl {v} = coe0→1 (λ i → α.Hom _ (coe0→i _ i v) v) refl

    Disc-LAssoc : LAssoc Disc-Pull Path-Pull
    Disc-LAssoc .assoc-l {x} v p q = subst (λ φ → α.Hom x (p ◁ q ◁ v) φ)
      (sym ( ap (λ ψ → transport ψ v) (ap sym (ap-comp-∙ _ p q) ∙ sym-∙ _ _)
           ∙ transport-comp _ _ v))
      refl

    -- TODO
    -- Disc-Pullbacks : Pullbacks (Disc A) α
    -- Disc-Pullbacks .Pullbacks.hp = Disc-Pull
    -- Disc-Pullbacks .pull-univ p v (u₁ , q₁) (u₂ , q₂) = {!!}

    {-# INCOHERENT Disc-Pull Disc-LAssoc #-}


-- -- TODO
-- module _ {ℓa ℓb} {A : I → Type ℓa} {B : ∀ i → A i → Type ℓb} where instance
--   Δᵈ-contravariant : is-contravariant-fibration (Δᵈ B)
--   Δᵈ-contravariant .lift⁻ p v .fst = coe1→0 (λ i → B i (p i)) v , λ i → coe1→i (λ j → B j (p j)) i v
--   Δᵈ-contravariant .lift⁻ p v .snd (u , q) = sym (from-pathᴾ⁻ q) ,ₚ {!!}

--   Δᵈ-covariant : is-covariant-fibration (Δᵈ B)
--   Δᵈ-covariant .lift⁺ p u .fst = coe0→1 (λ i → B i (p i)) u , λ i → coe0→i (λ j → B j (p j)) i u
--   Δᵈ-covariant .lift⁺ p u .snd (v , q) = sym (from-pathᴾ q) ,ₚ {!!}

-- {-# OVERLAPPING Δᵈ-contravariant Δᵈ-covariant #-}

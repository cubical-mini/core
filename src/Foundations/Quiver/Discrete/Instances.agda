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

open import Notation.Assoc.Left
open import Notation.Assoc.Right
open import Notation.Extend
open import Notation.Pull
open import Notation.Push
open import Notation.Refl
open import Notation.Sym

instance
  Disc-Refl : ∀{ℓ} {A : Type ℓ} → Refl (Disc A)
  Disc-Refl .refl = reflₚ

  Disc-Sym : ∀{ℓ} {A : Type ℓ} → Sym (Disc A) λ x y → Disc (x ＝ y)
  Disc-Sym .sym = symₚ
  Disc-Sym .sym-invol = refl

module _ {ℓa} {A : Type ℓa} where instance
  Path-Push : {x : A} → HPush (Disc A) 0 λ y → Disc (x ＝ y)
  Path-Push .push p q = q ∙ p
  Path-Push .push-refl {u} = id-o u

  Path-Pull : {y : A} → HPull (Disc A) 0 λ x → Disc (x ＝ y)
  Path-Pull .pull = _∙_
  Path-Pull .pull-refl {v} = id-i v

  Path-RAssoc : {x : A} → RAssoc (Disc A) λ y → Disc (x ＝ y)
  Path-RAssoc .assoc-r = assoc

  Path-LAssoc : {y : A} → LAssoc (Disc A) λ x → Disc (x ＝ y)
  Path-LAssoc .assoc-l v p q = assoc p q v

{-# OVERLAPPING
  Disc-Refl Disc-Sym
  Path-Push Path-Pull
  Path-RAssoc Path-LAssoc
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
    Disc-Push .push {lfs} p = coe0→1 (λ i → F (p i) lfs)
    Disc-Push .push-refl {u} = coe0→1 (λ i → α.Hom _ u (coe0→i _ i u)) refl

    Disc-RAssoc : RAssoc (Disc A) α
    Disc-RAssoc .assoc-r {z} u p q = subst (λ φ → α.Hom z (u ▷ (p ▷ q)) φ)
      (subst-comp (λ ψ → F ψ _) p q u) refl
    {-# INCOHERENT Disc-Push Disc-RAssoc #-}

  module Default-Pull where instance
    Disc-Pull : HPull (Disc A) k α
    Disc-Pull .pull p = coe1→0 (λ i → F (p i) _)
    Disc-Pull .pull-refl {v} = coe0→1 (λ i → α.Hom _ (coe0→i _ i v) v) refl

    Disc-LAssoc : LAssoc (Disc A) α
    Disc-LAssoc .assoc-l {x} v p q = subst (λ φ → α.Hom x (p ◁ q ◁ v) φ)
      (sym ( ap (λ ψ → transport ψ v) (ap sym (ap-comp-∙ _ p q) ∙ sym-∙ _ _)
           ∙ transport-comp _ _ v))
      refl
    {-# INCOHERENT Disc-Pull Disc-LAssoc #-}

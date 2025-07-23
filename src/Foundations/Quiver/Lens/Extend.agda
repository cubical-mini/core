{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Extend where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Dual.Base

open import Notation.Extend
open import Notation.Profunctor
open import Notation.Pull
open import Notation.Push
open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 3 (m , m , k , _)} {ℓ-homᶠ : ℓ-sig 4 (m , m , k , k , _)}
  {F : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → ob-sig (ℓ-obᶠ lxs lys)}
  (α : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} (p : Hom x y) → HQuiver-onω k (F p) (ℓ-homᶠ lxs lys))
  ⦃ _ : Refl C ⦄ where
  private module α {lxs} {lys} x y p = Quiver-onω (α {lxs} {lys} {x} {y} p)

  Disp± : ⦃ _ : Extend C k α ⦄ → HQuiver-onωᵈ C k (λ t → F refl) _
  Disp± .Quiver-onωᵈ.Het[_] {x} {y} p u v = α.Het x y p (extend-r p v) (extend-l p u)


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 2 (m , k , _)}
  {F : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ ls)}
  {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {α : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)}
  ⦃ _ : Refl C ⦄ ⦃ _ : ∀{ls} {t : Ob ls} → Refl (α t) ⦄ where instance

    Push→Extend : ⦃ _ : Push C k α ⦄ → Extend C k (λ {y = y} _ → α y)
    Push→Extend .extend-l = push
    Push→Extend .extend-r _ v = v
    Push→Extend .extend-refl = push-refl
    Push→Extend .extend-coh = refl

    Pull→Extend : ⦃ _ : Pull C k α ⦄ → Extend C k (λ {x = x} _ → α x)
    Pull→Extend .extend-l _ u = u
    Pull→Extend .extend-r = pull
    Pull→Extend .extend-refl = pull-refl
    Pull→Extend .extend-coh = pull-refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 3 (m , m , k , _)}
  {F : ∀{lxs lys} → Ob lxs → Ob lys → ob-sig (ℓ-obᶠ lxs lys)}
  ⦃ _ : Refl C ⦄ where

  module _ {ℓ-homᶠ : ℓ-sig 4 (m , m , k , k , _)}
    {α : ∀{lxs lys} (x : Ob lxs) (y : Ob lys) → HQuiver-onω k (F x y) (ℓ-homᶠ lxs lys)}
    ⦃ _ : ∀{ls} {t : Ob ls} → Refl (α t t) ⦄ where instance

    Profunctor→Extend : ⦃ _ : HProfunctor C C k α ⦄ → Extend C k (λ {x = x} {y = y} _ → α x y ᵒᵖ)
    Profunctor→Extend .extend-l = dimap refl
    Profunctor→Extend .extend-r p = dimap p refl
    Profunctor→Extend .extend-refl = refl
    Profunctor→Extend .extend-coh = dimap-refl

{-# INCOHERENT Push→Extend Pull→Extend Profunctor→Extend #-}

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 3 (m , m , k , _)} {ℓ-homᶠ : ℓ-sig 4 (m , m , k , k , _)}
  {F : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → ob-sig (ℓ-obᶠ lxs lys)}
  {α : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} (p : Hom x y) → HQuiver-onω k (F p) (ℓ-homᶠ lxs lys)}
  ⦃ _ : Refl C ⦄ ⦃ _ : Extend C k α ⦄ where instance

  Disp±-Reflᵈ : Reflᵈ (Disp± α)
  Disp±-Reflᵈ .reflᵈ = extend-refl
  {-# INCOHERENT Disp±-Reflᵈ #-} -- TODO check

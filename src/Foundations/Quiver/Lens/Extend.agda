{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Extend where

open import Foundations.Quiver.Base

open import Notation.Extend
open import Notation.Pull
open import Notation.Push
open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 3 (m , m , k , _)} {ℓ-homᶠ : ℓ-sig 4 (m , m , k , k , _)}
  {F : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → ob-sig (ℓ-obᶠ lxs lys)}
  (α : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} (p : Hom x y) → HQuiver-onω k (F p) (ℓ-homᶠ lxs lys))
  ⦃ _ : Reflω C ⦄ where
  private module α {lxs} {lys} x y p = Quiver-onω (α {lxs} {lys} {x} {y} p)

  Disp± : ⦃ _ : Extendω C k F ⦄ → HQuiver-onωᵈ C k (λ t → F refl) _
  Disp± .Quiver-onωᵈ.Het[_] {x} {y} p u v = α.Het x y p (extend-r p v) (extend-l p u)


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 2 (m , k , _)} {F : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ ls)}
  ⦃ _ : Reflω C ⦄ where

  module _ ⦃ _ : HPushω C k F ⦄ where instance
    Push→Extend : Extendω C k (λ {y = y} _ → F y)
    Push→Extend .extend-l = push
    Push→Extend .extend-r _ v = v

    Lawful-Push→Extend : {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
                         {α⁺ : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)}
                         ⦃ _ : Lawful-Pushω C α⁺ ⦄ ⦃ _ : ∀{ls} {t : Ob ls} → Reflω (α⁺ t)⦄
                       → Lawful-Extendω C (λ {y = y} _ → α⁺ y)
    Lawful-Push→Extend .extend-refl = push-refl
    Lawful-Push→Extend .extend-coh = refl

  module _ ⦃ _ : HPullω C k F ⦄ where instance
    Pull→Extend : Extendω C k (λ {x = x} _ → F x)
    Pull→Extend .extend-l _ u = u
    Pull→Extend .extend-r = pull

    Lawful-Pull→Extend : {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
                         {α⁻ : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)}
                         ⦃ _ : Lawful-Pullω C α⁻ ⦄
                       → Lawful-Extendω C (λ {x = x} _ → α⁻ x)
    Lawful-Pull→Extend .extend-refl = pull-refl
    Lawful-Pull→Extend .extend-coh = pull-refl

{-# INCOHERENT
  Push→Extend Lawful-Push→Extend
  Pull→Extend Lawful-Pull→Extend
#-}


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 3 (m , m , k , _)} {ℓ-homᶠ : ℓ-sig 4 (m , m , k , k , _)}
  {F : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → ob-sig (ℓ-obᶠ lxs lys)}
  {α : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} (p : Hom x y) → HQuiver-onω k (F p) (ℓ-homᶠ lxs lys)}
  ⦃ _ : Reflω C ⦄ ⦃ _ : Extendω C k F ⦄ ⦃ _ : Lawful-Extendω C α ⦄ where instance

  Disp±-Reflᵈ : Reflωᵈ (Disp± C α)
  Disp±-Reflᵈ .reflᵈ _ = extend-refl
  {-# INCOHERENT Disp±-Reflᵈ #-} -- TODO check

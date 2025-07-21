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
  {Hom[_] : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → ob-sig (ℓ-obᶠ lxs lys)}
  (F : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} (p : Hom x y) → HQuiver-onω k Hom[ p ] (ℓ-homᶠ lxs lys))
  ⦃ _ : Reflω C ⦄ where
  private module F {lxs} {lys} x y p = Quiver-onω (F {lxs} {lys} {x} {y} p)

  Disp± : ⦃ _ : Extendω C k Hom[_] ⦄ → HQuiver-onωᵈ Ob Hom k (λ t → Hom[ refl ]) _
  Disp± .Quiver-onωᵈ.Het[_] {x} {y} p u v = F.Het x y p (extend-r p v) (extend-l p u)


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 2 (m , k , _)} {Ob[_] : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ ls)}
  ⦃ _ : Reflω C ⦄ where

  module _ ⦃ _ : HPushω C k Ob[_] ⦄ where instance
    Push→Extend : Extendω C k (λ {y = y} _ → Ob[ y ])
    Push→Extend .extend-l = push
    Push→Extend .extend-r _ v = v

    Lawful-Push→Extend : {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
                         {F⁺ : ∀{ls} (t : Ob ls) → HQuiver-onω k Ob[ t ] (ℓ-homᶠ ls)}
                         ⦃ _ : Lawful-Pushω C F⁺ ⦄ ⦃ _ : ∀{ls} {x : Ob ls} → Reflω (F⁺ x)⦄
                       → Lawful-Extendω C (λ {y = y} _ → F⁺ y)
    Lawful-Push→Extend .extend-refl = push-refl
    Lawful-Push→Extend .extend-coh = refl

  module _ ⦃ _ : HPullω C k Ob[_] ⦄ where instance
    Pull→Extend : Extendω C k (λ {x = x} _ → Ob[ x ])
    Pull→Extend .extend-l _ u = u
    Pull→Extend .extend-r = pull

    Lawful-Pull→Extend : {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
                         {F⁻ : ∀{ls} (t : Ob ls) → HQuiver-onω k Ob[ t ] (ℓ-homᶠ ls)}
                         ⦃ _ : Lawful-Pullω C F⁻ ⦄
                       → Lawful-Extendω C (λ {x = x} _ → F⁻ x)
    Lawful-Pull→Extend .extend-refl = pull-refl
    Lawful-Pull→Extend .extend-coh = pull-refl

{-# INCOHERENT
  Push→Extend Lawful-Push→Extend
  Pull→Extend Lawful-Pull→Extend
#-}


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 3 (m , m , k , _)} {ℓ-homᶠ : ℓ-sig 4 (m , m , k , k , _)}
  {Hom[_] : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → ob-sig (ℓ-obᶠ lxs lys)}
  {F : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} (p : Hom x y) → HQuiver-onω k Hom[ p ] (ℓ-homᶠ lxs lys)}
  ⦃ _ : Reflω C ⦄ ⦃ _ : Extendω C k Hom[_] ⦄ ⦃ _ : Lawful-Extendω C F ⦄ where instance
  private module F {lxs} {lys} x y p = Quiver-onω (F {lxs} {lys} {x} {y} p)

  Disp±-Reflᵈ : Reflωᵈ C (Disp± C F)
  Disp±-Reflᵈ .reflᵈ _ = extend-refl
  {-# INCOHERENT Disp±-Reflᵈ #-} -- TODO check

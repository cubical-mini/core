{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Extend where

open import Foundations.Quiver.Base

open import Notation.Extend
open import Notation.Pull
open import Notation.Push
open import Notation.Refl

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  {n}
  {ℓ-obᶠ : Levels m → Levels m → ℓ-sig n} {ℓ-homᶠ : Levels m → Levels m → ℓ-sig² n n}
  {Hom[_] : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → ob-sig (ℓ-obᶠ lxs lys)}
  (F : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} (p : Hom x y) → HQuiver-onω n Hom[ p ] (ℓ-homᶠ lxs lys))
  ⦃ _ : Reflω C ⦄ where
  private module F {lxs} {lys} x y p = Quiver-onω (F {lxs} {lys} {x} {y} p)

  Disp± : ⦃ _ : Extendω C n Hom[_] ⦄ → HQuiver-onωᵈ Ob Hom n (λ t → Hom[ (refl {x = t}) ]) _
  Disp± .Quiver-onωᵈ.Het[_] {x} {y} p u v = F.Het x y p (extend-r p v) (extend-l p u)


module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {n} {ℓ-obᶠ : Levels m → ℓ-sig n}
  {Ob[_] : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ ls)}
  ⦃ _ : Reflω C ⦄ where

  module _ ⦃ _ : Pushω C n Ob[_] Ob[_] ⦄ where instance
    Push→Extend : Extendω C n (λ {y = y} _ → Ob[ y ])
    Push→Extend .extend-l = push
    Push→Extend .extend-r _ v = v

    Lawful-Push→Extend : {ℓ-homᶠ : Levels m → ℓ-sig² n n}
                         {F⁺ : ∀{ls} (t : Ob ls) → HQuiver-onω n Ob[ t ] (ℓ-homᶠ ls)}
                         ⦃ _ : Lawful-Pushω C F⁺ ⦄ ⦃ _ : ∀{ls} {x : Ob ls} → Reflω (F⁺ x)⦄
                       → Lawful-Extendω C (λ {y = y} _ → F⁺ y)
    Lawful-Push→Extend .extend-refl = push-refl
    Lawful-Push→Extend .extend-coh = refl

  module _ ⦃ _ : Pullω C n Ob[_] Ob[_] ⦄ where instance
    Pull→Extend : Extendω C n (λ {x = x} _ → Ob[ x ])
    Pull→Extend .extend-l _ u = u
    Pull→Extend .extend-r = pull

    Lawful-Pull→Extend : {ℓ-homᶠ : Levels m → ℓ-sig² n n}
                         {F⁻ : ∀{ls} (t : Ob ls) → HQuiver-onω n Ob[ t ] (ℓ-homᶠ ls)}
                         ⦃ _ : Lawful-Pullω C F⁻ ⦄
                       → Lawful-Extendω C (λ {x = x} _ → F⁻ x)
    Lawful-Pull→Extend .extend-refl = pull-refl
    Lawful-Pull→Extend .extend-coh = pull-refl

{-# INCOHERENT
  Push→Extend Lawful-Push→Extend
  Pull→Extend Lawful-Pull→Extend
#-}


module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {n}
  {ℓ-obᶠ : Levels m → Levels m → ℓ-sig n} {ℓ-homᶠ : Levels m → Levels m → ℓ-sig² n n}
  {Hom[_] : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → ob-sig (ℓ-obᶠ lxs lys)}
  {F : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} (p : Hom x y) → HQuiver-onω n Hom[ p ] (ℓ-homᶠ lxs lys)}
  ⦃ _ : Reflω C ⦄ ⦃ _ : Extendω C n Hom[_] ⦄ ⦃ _ : Lawful-Extendω C F ⦄ where instance
  private module F {lxs} {lys} x y p = Quiver-onω (F {lxs} {lys} {x} {y} p)

  Disp±-Reflᵈ : Reflωᵈ C (Disp± C F)
  Disp±-Reflᵈ .reflᵈ _ = extend-refl
  {-# INCOHERENT Disp±-Reflᵈ #-} -- TODO check

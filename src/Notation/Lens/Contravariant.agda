{-# OPTIONS --safe #-}
module Notation.Lens.Contravariant where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  n
  {ℓ-obᶠ⁻ ℓ-obᶠ⁺ : Levels m → ℓ-sig n}
  (Ob[_]⁻ : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ⁻ ls))
  (Ob[_]⁺ : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ⁺ ls)) where

  record Pull lxs lys lfs : Type
    (ℓ-ob lxs ⊔ ℓ-ob lys ⊔ ℓ-hom lxs lys ⊔ ℓ-obᶠ⁻ lxs lfs ⊔ ℓ-obᶠ⁺ lys lfs) where
    no-eta-equality
    field pull : {x : Ob lxs} {y : Ob lys} (p : Hom x y) → Ob[ y ]⁺ lfs → Ob[ x ]⁻ lfs

  Pullω : Typeω
  Pullω = ∀{lxs lys lfs} → Pull lxs lys lfs

open Pull ⦃ ... ⦄ public
{-# DISPLAY Pull.pull _ p u = pull p u #-}


module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  {n} {ℓ-obᶠ⁻ ℓ-obᶠ⁺ : Levels m → ℓ-sig n}
  {ℓ-hetᶠ : Levels m → ℓ-sig² n n}
  {Ob[_]⁻ : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ⁻ ls)}
  {Ob[_]⁺ : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ⁺ ls)}
  (F : ∀{ls} (t : Ob ls) → Quiver-onω n n Ob[ t ]⁻ Ob[ t ]⁺ (ℓ-hetᶠ ls))
  ⦃ _ : Reflω C ⦄ ⦃ _ : Pullω C n Ob[_]⁻ Ob[_]⁺ ⦄ where
  private module F {ls} t = Quiver-onω (F {ls} t)

  record Lawful-Pull ls lfs : Type (ℓ-ob ls ⊔ ℓ-obᶠ⁺ ls lfs ⊔ ℓ-hetᶠ ls lfs lfs) where
    no-eta-equality
    field pull-refl : {y : Ob ls} {v : Ob[ y ]⁺ lfs} → F.Het y (pull refl v) v

  Lawful-Pullω : Typeω
  Lawful-Pullω = ∀{ls lfs} → Lawful-Pull ls lfs

open Lawful-Pull ⦃ ... ⦄ public
{-# DISPLAY Lawful-Pull.pull-refl _ = pull-refl #-}

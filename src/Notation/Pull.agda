{-# OPTIONS --safe #-}
module Notation.Pull where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} (C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω C)
  k {ℓ-obᶠ⁻ : ℓ-sig 2 (m , k , _)} {ℓ-obᶠ⁺ : ℓ-sig 2 (n , k , _)}
  (Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᶠ⁻) (Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᶠ⁺) where

  record Pull lxs lys lfs : Type
    (ℓ-ob⁻ lxs ⊔ ℓ-ob⁺ lys ⊔ ℓ-het lxs lys ⊔ ℓ-obᶠ⁻ lxs lfs ⊔ ℓ-obᶠ⁺ lys lfs) where
    no-eta-equality
    field pull : {x : Ob⁻ lxs} {y : Ob⁺ lys} (p : Het x y) → Ob[ y ]⁺ lfs → Ob[ x ]⁻ lfs

    infixr 300 _◁_
    _◁_ : {x : Ob⁻ lxs} {y : Ob⁺ lys} → Het x y → Ob[ y ]⁺ lfs → Ob[ x ]⁻ lfs
    p ◁ α = pull p α

  Pullω : Typeω
  Pullω = ∀{lxs lys lfs} → Pull lxs lys lfs

open Pull ⦃ ... ⦄ public
{-# DISPLAY Pull.pull _ p u = pull p u #-}

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} (C : HQuiver-onω m Ob ℓ-hom) k where
  module _ {ℓ-obᶠ⁻ ℓ-obᶠ⁺} (Ob[_]⁻ : ob-sigᵈ Ob ℓ-obᶠ⁻) (Ob[_]⁺ : ob-sigᵈ Ob ℓ-obᶠ⁺) where
    SPull = Pull C k Ob[_]⁻ Ob[_]⁺
    SPullω = ∀{lxs lys lfs} → SPull lxs lys lfs

  module _ {ℓ-obᶠ} (Ob[_] : ob-sigᵈ Ob ℓ-obᶠ) where
    HPull = SPull Ob[_] Ob[_]
    HPullω = ∀{lxs lys lfs} → HPull lxs lys lfs


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} (C : HQuiver-onω m Ob ℓ-hom)
  {k ℓ-obᶠ⁻ ℓ-obᶠ⁺} {ℓ-hetᶠ : ℓ-sig 3 (m , k , k , _)}
  {Ob[_]⁻ : ob-sigᵈ Ob ℓ-obᶠ⁻} {Ob[_]⁺ : ob-sigᵈ Ob ℓ-obᶠ⁺}
  (F : ∀{ls} (t : Ob ls) → Quiver-onω k Ob[ t ]⁻ k Ob[ t ]⁺ (ℓ-hetᶠ ls))
  ⦃ _ : Reflω C ⦄ ⦃ _ : SPullω C k Ob[_]⁻ Ob[_]⁺ ⦄ where
  private module F {ls} t = Quiver-onω (F {ls} t)

  record Lawful-Pull ls lfs : Type (ℓ-ob ls ⊔ ℓ-obᶠ⁺ ls lfs ⊔ ℓ-hetᶠ ls lfs lfs) where
    no-eta-equality
    field pull-refl : {y : Ob ls} {v : Ob[ y ]⁺ lfs} → F.Het y (pull refl v) v

  Lawful-Pullω : Typeω
  Lawful-Pullω = ∀{ls lfs} → Lawful-Pull ls lfs

open Lawful-Pull ⦃ ... ⦄ public
{-# DISPLAY Lawful-Pull.pull-refl _ = pull-refl #-}


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k ℓ-obᶠ} {Ob[_] : ob-sigᵈ Ob ℓ-obᶠ}
  {lxs lys lfs} ⦃ _ : HPull C k Ob[_] lxs lys lfs ⦄ where

  infixr 400 _>$<_
  _>$<_ : {x : Ob lxs} {y : Ob lys} → Hom x y → Ob[ y ] lfs → Ob[ x ] lfs
  _>$<_ f my = pull f my

  infixl 400 _>&<_
  _>&<_ : {x : Ob lxs} {y : Ob lys} → Ob[ y ] lfs → Hom x y → Ob[ x ] lfs
  _>&<_ my f = pull f my

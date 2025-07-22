{-# OPTIONS --safe #-}
module Notation.Pull where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} (C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω C)
  k {ℓ-obᶠ : ℓ-sig 2 (m , k , _)} {ℓ-obᵍ : ℓ-sig 2 (n , k , _)}
  (F : ob-sigᵈ Ob⁻ ℓ-obᶠ) (G : ob-sigᵈ Ob⁺ ℓ-obᵍ) where

  record Pull lxs lys lfs : Type
    (ℓ-ob⁻ lxs ⊔ ℓ-ob⁺ lys ⊔ ℓ-het lxs lys ⊔ ℓ-obᶠ lxs lfs ⊔ ℓ-obᵍ lys lfs) where
    no-eta-equality
    field pull : {x : Ob⁻ lxs} {y : Ob⁺ lys} (p : Het x y) → G y lfs → F x lfs

    infixr 300 _◁_
    _◁_ : {x : Ob⁻ lxs} {y : Ob⁺ lys} → Het x y → G y lfs → F x lfs
    p ◁ α = pull p α

  Pullω : Typeω
  Pullω = ∀{lxs lys lfs} → Pull lxs lys lfs

open Pull ⦃ ... ⦄ public
{-# DISPLAY Pull.pull _ p u = pull p u #-}

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} (C : HQuiver-onω m Ob ℓ-hom) k where
  module _ {ℓ-obᶠ} (F : ob-sigᵈ Ob ℓ-obᶠ) where
    module _ {ℓ-obᵍ} (G : ob-sigᵈ Ob ℓ-obᵍ) where
      SPull  = Pull C k F G
      SPullω = ∀{lxs lys lfs} → SPull lxs lys lfs

    HPull  = SPull F
    HPullω = ∀{lxs lys lfs} → HPull lxs lys lfs


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} (C : HQuiver-onω m Ob ℓ-hom)
  {k ℓ-obᶠ ℓ-obᵍ} {ℓ-hetᶠ : ℓ-sig 3 (m , k , k , _)}
  {F : ob-sigᵈ Ob ℓ-obᶠ} {G : ob-sigᵈ Ob ℓ-obᵍ}
  (α : ∀{ls} (t : Ob ls) → Quiver-onω k (F t) k (G t) (ℓ-hetᶠ ls))
  ⦃ _ : Reflω C ⦄ ⦃ _ : SPullω C k F G ⦄ where
  private module α {ls} t = Quiver-onω (α {ls} t)

  record Lawful-Pull ls lfs : Type (ℓ-ob ls ⊔ ℓ-obᵍ ls lfs ⊔ ℓ-hetᶠ ls lfs lfs) where
    no-eta-equality
    field pull-refl : {y : Ob ls} {v : G y lfs} → α.Het y (pull refl v) v

  Lawful-Pullω : Typeω
  Lawful-Pullω = ∀{ls lfs} → Lawful-Pull ls lfs

open Lawful-Pull ⦃ ... ⦄ public
{-# DISPLAY Lawful-Pull.pull-refl _ = pull-refl #-}


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k ℓ-obᶠ} {F : ob-sigᵈ Ob ℓ-obᶠ}
  {lxs lys lfs} ⦃ _ : HPull C k F lxs lys lfs ⦄ where

  infixr 400 _>$<_
  _>$<_ : {x : Ob lxs} {y : Ob lys} → Hom x y → F y lfs → F x lfs
  _>$<_ f my = pull f my

  infixl 400 _>&<_
  _>&<_ : {x : Ob lxs} {y : Ob lys} → F y lfs → Hom x y → F x lfs
  _>&<_ my f = pull f my

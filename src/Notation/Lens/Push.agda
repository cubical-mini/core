{-# OPTIONS --safe #-}
module Notation.Lens.Push where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  n {ℓ-obᶠ⁻ ℓ-obᶠ⁺ : Levels m → ℓ-sig n}
  (Ob[_]⁻ : ob-sigᵈ Ob ℓ-obᶠ⁻) (Ob[_]⁺ : ob-sigᵈ Ob ℓ-obᶠ⁺) where

  record Push lxs lys lfs : Type
    (ℓ-ob lxs ⊔ ℓ-ob lys ⊔ ℓ-hom lxs lys ⊔ ℓ-obᶠ⁻ lxs lfs ⊔ ℓ-obᶠ⁺ lys lfs) where
    no-eta-equality
    field push : {x : Ob lxs} {y : Ob lys} (p : Hom x y) → Ob[ x ]⁻ lfs → Ob[ y ]⁺ lfs

  Pushω : Typeω
  Pushω = ∀{lxs lys lfs} → Push lxs lys lfs

open Push ⦃ ... ⦄ public
{-# DISPLAY Push.push _ p u = push p u #-}


module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  {n} {ℓ-obᶠ⁻ ℓ-obᶠ⁺ : Levels m → ℓ-sig n} {ℓ-hetᶠ : Levels m → ℓ-sig² n n}
  {Ob[_]⁻ : ob-sigᵈ Ob ℓ-obᶠ⁻} {Ob[_]⁺ : ob-sigᵈ Ob ℓ-obᶠ⁺}
  (F : ∀{ls} (t : Ob ls) → Quiver-onω n n Ob[ t ]⁻ Ob[ t ]⁺ (ℓ-hetᶠ ls))
  ⦃ _ : Reflω C ⦄ ⦃ _ : Pushω C n Ob[_]⁻ Ob[_]⁺ ⦄ where
  private module F {ls} t = Quiver-onω (F {ls} t)

  record Lawful-Push ls lfs : Type (ℓ-ob ls ⊔ ℓ-obᶠ⁻ ls lfs ⊔ ℓ-hetᶠ ls lfs lfs) where
    no-eta-equality
    field push-refl : {x : Ob ls} {u : Ob[ x ]⁻ lfs} → F.Het x u (push refl u)

  Lawful-Pushω : Typeω
  Lawful-Pushω = ∀{ls lfs} → Lawful-Push ls lfs

open Lawful-Push ⦃ ... ⦄ public
{-# DISPLAY Lawful-Push.push-refl _ = push-refl #-}


module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  n {ℓ-obᶠ : Levels m → ℓ-sig n} (Ob[_] : ob-sigᵈ Ob ℓ-obᶠ) where

  HPush = Push C n Ob[_] Ob[_]
  HPushω = ∀{lxs lys lfs} → HPush lxs lys lfs

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {n} {ℓ-obᶠ : Levels m → ℓ-sig n} {Ob[_] : ob-sigᵈ Ob ℓ-obᶠ}
  {lxs lys lfs} ⦃ _ : HPush C n Ob[_] lxs lys lfs ⦄ where

  infixr 400 _<$>_
  _<$>_ : {x : Ob lxs} {y : Ob lys} → Hom x y → Ob[ x ] lfs → Ob[ y ] lfs
  _<$>_ f mx = push f mx

  infixl 400 _<&>_
  _<&>_ : {x : Ob lxs} {y : Ob lys} → Ob[ x ] lfs → Hom x y → Ob[ y ] lfs
  _<&>_ mx f = push f mx

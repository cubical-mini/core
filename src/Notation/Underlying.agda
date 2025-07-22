{-# OPTIONS --safe #-}
module Notation.Underlying where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Type

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-het}
  (C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω C) where

  record Underlying : Typeω where
    constructor mk-underlying
    no-eta-equality
    field
      {ℓ-und⁻} : Levels m → Level
      {ℓ-und⁺} : Levels n → Level
      ⌞_⌟⁻     : ∀{lxs} (x : Ob⁻ lxs) → Type (ℓ-und⁻ lxs)
      ⌞_⌟⁺     : ∀{lys} (y : Ob⁺ lys) → Type (ℓ-und⁺ lys)
      ⌞_⌟₁     : ∀{lxs lys} {x : Ob⁻ lxs} {y : Ob⁺ lys}
               → (p : Het x y) → ⌞ x ⌟⁻ → ⌞ y ⌟⁺

open Underlying ⦃ ... ⦄ public

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} where
  module _ (C : HQuiver-onω m Ob ℓ-hom) where
    HUnderlying = Underlying C

  module _ {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom)) where
    module _ (ℓ-und : Levels m → Level) (⌞_⌟ : ∀{ls} (t : Ob ls) → Type (ℓ-und ls))
      (⌞_⌟₁ : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → ⌞ x ⌟ → ⌞ y ⌟) where
      mk-hunderlying : HUnderlying C
      mk-hunderlying = mk-underlying ⌞_⌟ ⌞_⌟ ⌞_⌟₁

    module _ ⦃ _ : Underlying C ⦄ where
      ⌞_⌟ = ⌞_⌟⁺

{-# DISPLAY Underlying.⌞_⌟⁻ _ = ⌞_⌟ #-}
{-# DISPLAY Underlying.⌞_⌟⁺ _ = ⌞_⌟ #-}
{-# DISPLAY Underlying.⌞_⌟₁ _ = ⌞_⌟ #-}


instance
  Funs-Underlying : Underlying Funs
  Funs-Underlying = mk-hunderlying fst id id

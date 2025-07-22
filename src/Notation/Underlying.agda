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
      { ℓ-und⁻ } : Levels m → Level
      { ℓ-und⁺ } : Levels n → Level
      ⌞_⌟⁻       : ∀{lfs} (x : Ob⁻ lfs) → Type (ℓ-und⁻ lfs)
      ⌞_⌟⁺       : ∀{lfs} (x : Ob⁺ lfs) → Type (ℓ-und⁺ lfs)

open Underlying ⦃ ... ⦄ public

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} where
  module _ (C : HQuiver-onω m Ob ℓ-hom) where
    HUnderlying = Underlying C

  module _ {C : HQuiver-onω m Ob ℓ-hom} where
    module _ (ℓ-und : Levels m → Level) (⌞_⌟ : ∀{lfs} (x : Ob lfs) → Type (ℓ-und lfs)) where
      mk-hunderlying : HUnderlying C
      mk-hunderlying = mk-underlying ⌞_⌟ ⌞_⌟

    module _ ⦃ _ : Underlying C ⦄ where
      ⌞_⌟ = ⌞_⌟⁺

{-# DISPLAY Underlying.⌞_⌟⁻ _ = ⌞_⌟ #-}
{-# DISPLAY Underlying.⌞_⌟⁺ _ = ⌞_⌟ #-}


instance
  Funs-Underlying : Underlying Funs
  Funs-Underlying = mk-hunderlying fst id

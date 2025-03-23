{-# OPTIONS --safe #-}
module Control.Displayed.Reflexivity where

open import Prim.Type

open import Control.Structures.Quiver
open import Control.Reflexivity

module _ {Q : Quiver} ⦃ _ : Refl Q ⦄ where
  open Quiver Q

  module _
    {ob-lvlᴰ : Level → Level }
    {hom-lvlᴰ : Level → Level → Level }
    (Ob[_] : ∀ {ℓ} → Ob ℓ → Type (ob-lvlᴰ ℓ))
    (Hom[_] : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} → Hom x y → Ob[ x ] → Ob[ y ] → Type (hom-lvlᴰ ℓx ℓy))
    where

    record Reflᴰ : Typeω where
      no-eta-equality
      field reflᴰ : {ℓx : Level} {x : Ob ℓx} {x′ : Ob[ x ]} → Hom[ refl ] x′ x′

open Reflᴰ ⦃ ... ⦄ public

{-# DISPLAY Reflᴰ.reflᴰ _ = reflᴰ #-}

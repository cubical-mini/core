{-# OPTIONS --safe #-}
module Control.Equiv.External where

open import Prim.Type

open import Control.Composition
open import Control.Diagram.Product.Binary
open import Control.Invertibility.External

open import Lib.HLevel.Base

private variable ℓx ℓy : Level

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  {Ob  : (ℓ : Level) → Type (ob-lvl ℓ)}
  {Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy)}
  ⦃ _ : Comp Ob Hom ⦄ (ℓ : Level) {x : Ob ℓx} {y : Ob ℓy} (f : Hom x y)
  where

  is-equiv : Type (ob-lvl ℓ ⊔ hom-lvl ℓx ℓ ⊔ hom-lvl ℓy ℓ ⊔ hom-lvl ℓ ℓx ⊔ hom-lvl ℓ ℓy)
  is-equiv = is-inv-o ℓ f × is-inv-i ℓ f

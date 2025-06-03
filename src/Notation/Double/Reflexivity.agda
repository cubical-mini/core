{-# OPTIONS --safe #-}
module Notation.Double.Reflexivity where

open import Prim.Type

open import Notation.Base
open import Notation.Double.Base
open import Notation.Reflexivity

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-sq : ℓ-sq-sig}
  (C : ℚuiver-on Ob ℓ-sq) (open ℚuiver-on C)
  (ℓx ℓy : Level)
  ⦃ _ : Refl Quiverₕ ℓx ⦄ ⦃ _ : Refl Quiverₕ ℓy ⦄
  ⦃ _ : Refl Quiverᵥ ℓx ⦄ ⦃ _ : Refl Quiverᵥ ℓy ⦄ where

  record ℝefl : Type (ℓ-ob ℓx l⊔ ℓ-ob ℓy l⊔ ℓ-ver ℓ-sq ℓx ℓy l⊔ ℓ-hor ℓ-sq ℓx ℓy) where
    no-eta-equality
    field
      reflₕ : {x : Ob ℓx} {y : Ob ℓy} {f : Ver x y} → Sq refl f f refl
      reflᵥ : {x : Ob ℓx} {y : Ob ℓy} {f : Hor x y} → Sq f refl refl f

open ℝefl ⦃ ... ⦄ public

{-# DISPLAY ℝefl.reflₕ _ = reflₕ #-}
{-# DISPLAY ℝefl.reflᵥ _ = reflᵥ #-}

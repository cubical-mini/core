{-# OPTIONS --safe #-}
module Notation.Double.Reflexivity where

open import Prim.Type

open import Notation.Double.Quiver
open import Notation.Quiver
open import Notation.Reflexivity

module _ {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) {ℓ-hom□ : ℓ-square-sig}
  {Homₕ : hom-sig Ob (ℓ-homₕ ℓ-hom□)} ⦃ _ : Refl Ob Homₕ ⦄
  {Homᵥ : hom-sig Ob (ℓ-homᵥ ℓ-hom□)} ⦃ _ : Refl Ob Homᵥ ⦄
  (Hom□ : square-sig Ob Homₕ Homᵥ ℓ-hom□)
  where

  record ℝefl : Typeω where
    no-eta-equality
    field
      reflₕ : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} {f : Homᵥ x y} → Hom□ refl f f refl
      reflᵥ : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} {f : Homₕ x y} → Hom□ f refl refl f

open ℝefl ⦃ ... ⦄ public

{-# DISPLAY ℝefl.reflₕ _ = reflₕ #-}
{-# DISPLAY ℝefl.reflᵥ _ = reflᵥ #-}

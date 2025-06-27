{-# OPTIONS --safe #-}
module Notation.Refl where

open import Foundations.Quiver.Base

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom)) where

  record Refl ls : Type (ℓ-ob ls ⊔ ℓ-hom ls ls) where
    no-eta-equality
    field refl : {x : Ob ls} → Hom x x

  Reflω : Typeω
  Reflω = ∀{ls} → Refl ls

open Refl ⦃ ... ⦄ public
{-# DISPLAY Refl.refl _ = refl #-}


module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  {m′ n′ ℓ-obᵈ⁻ ℓ-obᵈ⁺ ℓ-hetᵈ} {Ob[_]⁻ : ob-sigᵈ Ob ℓ-obᵈ⁻} {Ob[_]⁺ : ob-sigᵈ Ob ℓ-obᵈ⁺}
  (D : Quiver-onωᵈ Ob Ob Hom m′ n′ Ob[_]⁻ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D)
  ⦃ _ : Reflω C ⦄ where

  record Reflᵈ ls lsᵈ⁻ lsᵈ⁺ : Type
    (ℓ-ob ls ⊔ ℓ-obᵈ⁻ ls lsᵈ⁻ ⊔ ℓ-obᵈ⁺ ls lsᵈ⁺ ⊔ ℓ-hetᵈ ls ls lsᵈ⁻ lsᵈ⁺) where
    no-eta-equality
    field reflᵈ : {x : Ob ls} (x⁻ : Ob[ x ]⁻ lsᵈ⁻) (x⁺ : Ob[ x ]⁺ lsᵈ⁺) → Het[ refl ] x⁻ x⁺

  Reflωᵈ = ∀{ls lsᵈ⁻ lsᵈ⁺} → Reflᵈ ls lsᵈ⁻ lsᵈ⁺

open Reflᵈ ⦃ ... ⦄ public
{-# DISPLAY Reflᵈ.reflᵈ _ = reflᵈ #-}

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
  {m′ ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  (D : HQuiver-onωᵈ Ob Hom m′ Ob[_] ℓ-homᵈ) (open Quiver-onωᵈ D renaming (Het[_] to Hom[_]))
  ⦃ _ : Reflω C ⦄ where

  record Reflᵈ ls lsᵈ : Type (ℓ-ob ls ⊔ ℓ-obᵈ ls lsᵈ ⊔ ℓ-homᵈ ls ls lsᵈ lsᵈ) where
    no-eta-equality
    field reflᵈ : {x : Ob ls} (x′ : Ob[ x ] lsᵈ) → Hom[ refl ] x′ x′

  Reflωᵈ = ∀{ls lsᵈ} → Reflᵈ ls lsᵈ

open Reflᵈ ⦃ ... ⦄ public
{-# DISPLAY Reflᵈ.reflᵈ _ = reflᵈ #-}

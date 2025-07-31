{-# OPTIONS --safe #-}
module Notation.Refl where

open import Foundations.Quiver.Base

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom)) where

  record Refl : Typeω where
    no-eta-equality
    field refl : ∀{ls} {x : Ob ls} → Hom x x

open Refl ⦃ ... ⦄ public
{-# DISPLAY Refl.refl _ = refl #-}


module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {m′ ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  (D : HQuiver-onωᵈ C m′ Ob[_] ℓ-homᵈ) (open Quiver-onωᵈ D renaming (Het[_] to Hom[_]))
  ⦃ _ : Refl C ⦄ where

  record Reflᵈ : Typeω where
    no-eta-equality
    field reflᵈ : ∀{ls lsᵈ} {x : Ob ls} {x′ : Ob[ x ] lsᵈ} → Hom[ refl ] x′ x′

open Reflᵈ ⦃ ... ⦄ public
{-# DISPLAY Reflᵈ.reflᵈ _ = reflᵈ #-}

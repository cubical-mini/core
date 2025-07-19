{-# OPTIONS --safe #-}
module Foundations.Quiver.Section.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Section.Base

open import Notation.Extend
open import Notation.Refl

module _ {ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω 0 Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  {D : HQuiver-onωᵈ Ob Hom 0 Ob[_] ℓ-homᵈ} (open Quiver-onωᵈ D renaming (Het[_] to Hom[_]))
  where instance

  -- FIXME huh?!
  Π-Refl : ⦃ _ : Reflω C ⦄ ⦃ _ : Reflωᵈ C D ⦄
           ⦃ _ : {f : (x : Ob _) → Ob[ x ] _} → Extendω C 0 λ {x = x} {y = y} p _ → Hom[ p ] (f x) (f y) ⦄
         → Reflω (Π C D)
  Π-Refl .refl {x = f} u v p = extend-r p (reflᵈ (f v))

{-# INCOHERENT Π-Refl #-}

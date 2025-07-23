{-# OPTIONS --safe #-}
module Foundations.Quiver.Section.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Section.Base

open import Notation.Extend
open import Notation.Refl

-- FIXME
-- module _ {ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
--   {C : HQuiver-onω 0 Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
--   {ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
--   {D : HQuiver-onωᵈ C 0 Ob[_] ℓ-homᵈ} (open Quiver-onωᵈ D renaming (Het[_] to Hom[_]))
--   where instance

--   -- FIXME huh?!
--   Π-Refl : ⦃ _ : Refl C ⦄ ⦃ _ : Reflᵈ D ⦄
--            ⦃ _ : {f : (x : Ob _) → Ob[ x ] _} → Extend C 0 λ {x = x} {y = y} p _ → Hom[ p ] (f x) (f y) ⦄
--          → Refl (Π C D)
--   Π-Refl .refl {x = f} u v p = extend-r p (reflᵈ {x′ = f v})

-- {-# INCOHERENT Π-Refl #-}

{-# OPTIONS --safe #-}
module Foundations.Quiver.Component.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Component.Base

open import Notation.Refl

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {m′ ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  {D : HQuiver-onωᵈ Ob Hom m′ Ob[_] ℓ-homᵈ}
  ⦃ _ : Reflω C ⦄ ⦃ _ : Reflωᵈ C D ⦄ where instance

  Component-Refl : ∀{ls} {t : Ob ls} → Reflω (Component D t) -- canonical way
  Component-Refl .refl = reflᵈ _
  {-# INCOHERENT Component-Refl #-} -- TODO is it really necessary?

  -- TODO Component-Sym, Component-Comp

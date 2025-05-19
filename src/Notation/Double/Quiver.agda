{-# OPTIONS --safe #-}
module Notation.Double.Quiver where

open import Prim.Type

open import Notation.Quiver

ℓ-square-sig = Level → Level → Level → Level → Level

--         f
--    W----|--->X
--    |         |
--  g |    α    | h
--    v         v
--    Y----|--->Z
--         k
square-sig
  : {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob)
    {ℓ-homₕ : ℓ-hom-sig} (Homₕ : hom-sig Ob ℓ-homₕ)
    {ℓ-homᵥ : ℓ-hom-sig} (Homᵥ : hom-sig Ob ℓ-homᵥ)
  → (ℓ-hom□ : ℓ-square-sig) → Typeω
square-sig Ob Homₕ Homᵥ ℓ-hom□
  = {ℓw ℓx ℓy ℓz : Level} {W : Ob ℓw} {X : Ob ℓx} (f : Homₕ W X)
    {Y : Ob ℓy} (g : Homᵥ W Y) {Z : Ob ℓz} (h : Homᵥ X Z) (k : Homₕ Y Z)
  → Type (ℓ-hom□ ℓw ℓx ℓy ℓz)
{-# INLINE square-sig #-}

ℓ-homₕ : ℓ-square-sig → ℓ-hom-sig
ℓ-homₕ ℓ-hom□ ℓx ℓy = ℓ-hom□ ℓx ℓy ℓx ℓy

ℓ-homᵥ : ℓ-square-sig → ℓ-hom-sig
ℓ-homᵥ ℓ-hom□ ℓx ℓy = ℓ-hom□ ℓx ℓx ℓy ℓy

-- tight arrows are vertical, loose proarrows are horizontal
record ℚuiver-on {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) : Typeω where
  constructor mk-𝕢uiver
  no-eta-equality
  field {ℓ-hom□} : ℓ-square-sig

  field
    Homₕ : hom-sig Ob (ℓ-homₕ ℓ-hom□)
    Homᵥ : hom-sig Ob (ℓ-homᵥ ℓ-hom□)
    Hom□ : square-sig Ob Homₕ Homᵥ ℓ-hom□

  Quiverₕ : Quiver-on Ob
  Quiverₕ .Quiver-on.ℓ-hom = ℓ-homₕ ℓ-hom□
  Quiverₕ .Quiver-on.Hom = Homₕ

  Quiverᵥ : Quiver-on Ob
  Quiverᵥ .Quiver-on.ℓ-hom = ℓ-homᵥ ℓ-hom□
  Quiverᵥ .Quiver-on.Hom = Homᵥ

{-# OPTIONS --safe #-}
module Notation.Double.Base where

open import Prim.Type

open import Notation.Base

ℓ-sq-sig = Level → Level → Level → Level → Level

--         f
--    W----|--->X
--    |         |
--  g |    α    | h
--    v         v
--    Y----|--->Z
--         k
sq-sig
  : {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob)
    {ℓ-hor : ℓ-hom-sig} (Hor : hom-sig Ob ℓ-hor)
    {ℓ-ver : ℓ-hom-sig} (Ver : hom-sig Ob ℓ-ver)
  → (ℓ-sq : ℓ-sq-sig) → Typeω
sq-sig Ob Hor Ver ℓ-sq
  = ∀{ℓw ℓx ℓy ℓz} {W : Ob ℓw} {X : Ob ℓx} (f : Hor W X)
    {Y : Ob ℓy} (g : Ver W Y) {Z : Ob ℓz} (h : Ver X Z) (k : Hor Y Z)
  → Type (ℓ-sq ℓw ℓx ℓy ℓz)
{-# INLINE sq-sig #-}

ℓ-hor : ℓ-sq-sig → ℓ-hom-sig
ℓ-hor ℓ-sq ℓx ℓy = ℓ-sq ℓx ℓy ℓx ℓy
{-# NOINLINE ℓ-hor #-}

ℓ-ver : ℓ-sq-sig → ℓ-hom-sig
ℓ-ver ℓ-sq ℓx ℓy = ℓ-sq ℓx ℓx ℓy ℓy
{-# NOINLINE ℓ-ver #-}

-- tight arrows are vertical, loose proarrows are horizontal
record ℚuiver-on {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) (ℓ-sq : ℓ-sq-sig): Typeω where
  constructor mk-𝕢uiver
  no-eta-equality
  field
    Quiverₕ : Quiver-on Ob (ℓ-hor ℓ-sq)
    Quiverᵥ : Quiver-on Ob (ℓ-ver ℓ-sq)

  open Quiver-on Quiverₕ renaming (Hom to Hor) public
  open Quiver-on Quiverᵥ renaming (Hom to Ver) public

  field Sq : sq-sig Ob Hor Ver ℓ-sq


-- TODO
-- 2-sq-sig : ?
-- 2-sq-sig Ob = {ℓw ℓx ℓy ℓz : Level} {w : Ob ℓw} {x : Ob ℓx} {f : Hor w x} {y : Ob ℓy} {g : Ver w y} {z : Ob ℓz} {h : Ver x z} {k : Hor y z} (α β : Sq f g h k) → Type (ℓ-sq ℓw ℓx ℓy ℓz)

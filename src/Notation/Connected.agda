{-# OPTIONS --safe #-}
module Notation.Connected where

open import Prim.Interval
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Strict
open import Notation.Symmetry

-- coherent when strict, can be used for instance resolution
module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (CC : 2-Quiver-on C) (open 2-Quiver-on CC) where

  record Connected ℓx ℓy : Type (ℓ-ob ℓx l⊔ ℓ-ob ℓy l⊔ ℓ-hom ℓx ℓy) where
    no-eta-equality
    constructor mk-connected
    field
      centre      : {x : Ob ℓx} {y : Ob ℓy} → Hom x y
      centre-cell : {x : Ob ℓx} {y : Ob ℓy} (f : Hom x y) → 2-Hom centre f

  Connectedω : Typeω
  Connectedω = ∀{ℓx ℓy} → Connected ℓx ℓy

open Connected public


module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {CC : 2-Quiver-on C} (open 2-Quiver-on CC) ⦃ co : Connectedω C CC ⦄
  where instance

  Connected→Refl : Reflω C
  Connected→Refl .refl = co .centre

  Connected→Sym : Symmetryω C
  Connected→Sym .sym _ = co .centre

  Connected→Comp : Compω C
  Connected→Comp ._∙_ _ _ = co .centre
{-# INCOHERENT Connected→Refl Connected→Sym Connected→Comp #-}


module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  where instance

  Connected⁻ : ⦃ co : Connectedω C Strict ⦄ → Connectedω C (Strict ²ᵒᵖω)
  Connected⁻ ⦃ co ⦄ .centre = co .centre
  Connected⁻ ⦃ co ⦄ .centre-cell f i = co .centre-cell f (~ i)
  {-# INCOHERENT Connected⁻ #-}

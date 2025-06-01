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

  record Connected ℓ ℓ′ : Type (ℓ-ob ℓ l⊔ ℓ-ob ℓ′ l⊔ ℓ-hom ℓ ℓ′) where
    no-eta-equality
    constructor mk-connected
    field
      centre      : {x : Ob ℓ} {y : Ob ℓ′} → Hom x y
      centre-cell : {x : Ob ℓ} {y : Ob ℓ′} (f : Hom x y) → 2-Hom centre f

open Connected public

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {CC : 2-Quiver-on C} (open 2-Quiver-on CC) where instance

  Connected→Refl : {ℓ : Level} ⦃ co : Connected C CC ℓ ℓ ⦄ → Refl C ℓ
  Connected→Refl ⦃ co ⦄ .refl = co .centre

  Connected→Sym : {ℓx ℓy : Level} ⦃ co : Connected C CC ℓx ℓy ⦄ → Symmetry C ℓy ℓx
  Connected→Sym ⦃ co ⦄ .sym _ = co .centre

  Connected→Comp : {ℓx ℓy ℓz : Level} ⦃ co : Connected C CC ℓx ℓz ⦄ → Comp C ℓx ℓy ℓz
  Connected→Comp ⦃ co ⦄ ._∙_ _ _ = co .centre
{-# INCOHERENT Connected→Refl Connected→Sym Connected→Comp #-}


module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓx ℓy : Level} where instance

  Connected⁻ : ⦃ co : Connected C Strict ℓx ℓy ⦄ → Connected C (Strict ²ᵒᵖω) ℓx ℓy
  Connected⁻ ⦃ co ⦄ .centre = co .centre
  Connected⁻ ⦃ co ⦄ .centre-cell f i = co .centre-cell f (~ i)
  {-# INCOHERENT Connected⁻ #-}

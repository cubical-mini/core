{-# OPTIONS --safe #-}
module Notation.Isomorphism where

open import Prim.Kan
open import Prim.Type

open import Notation.Adjoint
open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Duality
open import Notation.Idempotent
open import Notation.Invertibility.Quasi
open import Notation.Invertibility.Retraction
open import Notation.Invertibility.Section
open import Notation.Reflexivity
open import Notation.Retract
open import Notation.Strict
open import Notation.Symmetry
open import Notation.Unitality.Inner
open import Notation.Unitality.Outer

-- TODO levels?
module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄
  ⦃ _ : ∀{ℓw ℓx ℓy ℓz} → Assoc C Strict ℓw ℓx ℓy ℓz ⦄
  ⦃ _ : ∀{ℓx ℓy} → Unit-i C Strict ℓx ℓy ⦄ ⦃ _ : ∀{ℓx ℓy} → Unit-o C Strict ℓx ℓy ⦄
  where
  open Quasi-inverse

  Isos : Quiver-on Ob _
  Isos .Quiver-on.Hom x y = x ≅ y

  module Iso-quiver where
    instance
      Iso-Refl : ⦃ _ : {ℓ : Level} {x : Ob ℓ} → Idem C Strict {x = x} refl ⦄ → Reflω Isos
      Iso-Refl .refl .hom = refl
      Iso-Refl .refl .preserves .from = refl
      Iso-Refl .refl .preserves .to-from = idem
      Iso-Refl .refl .preserves .from-to = idem

      Iso-Symmetry : Symmetryω Isos
      Iso-Symmetry .sym e .hom = e .preserves .from
      Iso-Symmetry .sym e .preserves .from = e .hom
      Iso-Symmetry .sym e .preserves .to-from = e .preserves .from-to
      Iso-Symmetry .sym e .preserves .from-to = e .preserves .to-from

      Iso-Dual : {ℓx ℓy : Level} → Dual Isos Strict ℓx ℓy
      Iso-Dual .invol e _ .hom = e .hom
      Iso-Dual .invol e _ .preserves .from = e .preserves .from
      Iso-Dual .invol e _ .preserves .to-from = e .preserves .to-from
      Iso-Dual .invol e _ .preserves .from-to = e .preserves .from-to

    iso→retract : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} → x ≅ y → x Retract-of y
    iso→retract e .hom = e .hom
    iso→retract e .preserves .retraction = e .preserves .from
    iso→retract e .preserves .retraction-cell = e .preserves .to-from

    iso→retract⁻ : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} → x ≅ y → y Retract-of x
    iso→retract⁻ e = iso→retract (sym e)

    open Retract-quiver
    instance
      Iso-Comp : Compω Isos
      Iso-Comp ._∙_ f g .hom = f .hom ∙ g .hom
      Iso-Comp ._∙_ f g .preserves .from = g .preserves .from ∙ f .preserves .from
      Iso-Comp ._∙_ f g .preserves .to-from = (iso→retract  f ∙ iso→retract  g) .preserves .retraction-cell
      Iso-Comp ._∙_ f g .preserves .from-to = (iso→retract⁻ g ∙ iso→retract⁻ f) .preserves .retraction-cell

    {-# INCOHERENT
      Iso-Refl Iso-Symmetry Iso-Comp
      Iso-Dual
    #-}

{-# OPTIONS --safe #-}
module Notation.Isomorphism.Reasoning where

open import Prim.Kan
open import Prim.Type

open import Notation.Adjoint
open import Notation.Adjoint.Strict
open import Notation.Associativity
open import Notation.Associativity.Strict
open import Notation.Base
open import Notation.Composition
open import Notation.Duality
open import Notation.Idempotent
open import Notation.Isomorphism
open import Notation.Reflexivity
open import Notation.Retract
open import Notation.Retract.Reasoning
open import Notation.Strict
open import Notation.Symmetry
open import Notation.Unitality.Inner
open import Notation.Unitality.Inner.Strict
open import Notation.Unitality.Outer
open import Notation.Unitality.Outer.Strict
open import Notation.Whiskering.Left.Strict
open import Notation.Whiskering.Right.Strict

open import Foundations.Path.Interface

-- TODO levels?
module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄
  ⦃ _ : ∀{ℓw ℓx ℓy ℓz} → Assoc C Strict ℓw ℓx ℓy ℓz ⦄
  ⦃ _ : ∀{ℓx ℓy} → Unit-i C Strict ℓx ℓy ⦄ ⦃ _ : ∀{ℓx ℓy} → Unit-o C Strict ℓx ℓy ⦄
  where

  iso→retract : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} → x ≅ y → x Retract-of y
  iso→retract e ._Retract-of_.to = e ._≅_.to
  iso→retract e ._Retract-of_.from = e ._≅_.from
  iso→retract e ._Retract-of_.retract-cell = sym (e ._≅_.inverses .Adjoint.η)

  Isos : Quiver-on Ob _
  Isos .Quiver-on.Hom x y = x ≅ y

  instance
    Iso-Refl : ⦃ _ : {ℓ : Level} {x : Ob ℓ} → Idem C Strict {x = x} refl ⦄ → Reflω Isos
    Iso-Refl .refl ._≅_.to = refl
    Iso-Refl .refl ._≅_.from = refl
    Iso-Refl .refl ._≅_.inverses .Adjoint.η = sym idem
    Iso-Refl .refl ._≅_.inverses .Adjoint.ε = idem
    Iso-Refl .refl ._≅_.inverses .Adjoint.zig = _
    Iso-Refl .refl ._≅_.inverses .Adjoint.zag = _

    Iso-Symmetry : Symmetryω Isos
    Iso-Symmetry .sym f ._≅_.to = f ._≅_.from
    Iso-Symmetry .sym f ._≅_.from = f ._≅_.to
    Iso-Symmetry .sym f ._≅_.inverses .Adjoint.η = sym (f ._≅_.inverses .Adjoint.ε)
    Iso-Symmetry .sym f ._≅_.inverses .Adjoint.ε = sym (f ._≅_.inverses .Adjoint.η)
    Iso-Symmetry .sym f ._≅_.inverses .Adjoint.zig = _
    Iso-Symmetry .sym f ._≅_.inverses .Adjoint.zag = _

    Iso-Dual : {ℓx ℓy : Level} → Dual Isos Strict ℓx ℓy
    Iso-Dual .invol f _ ._≅_.to = f ._≅_.to
    Iso-Dual .invol f _ ._≅_.from = f ._≅_.from
    Iso-Dual .invol f _ ._≅_.inverses .Adjoint.η = f ._≅_.inverses .Adjoint.η
    Iso-Dual .invol f _ ._≅_.inverses .Adjoint.ε = f ._≅_.inverses .Adjoint.ε
    Iso-Dual .invol f _ ._≅_.inverses .Adjoint.zig = _
    Iso-Dual .invol f _ ._≅_.inverses .Adjoint.zag = _

  iso→retract⁻ : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} → x ≅ y → y Retract-of x
  iso→retract⁻ e = iso→retract (sym e)

  instance
    Iso-Comp : Compω Isos
    Iso-Comp ._∙_ f g ._≅_.to = f ._≅_.to ∙ g ._≅_.to
    Iso-Comp ._∙_ f g ._≅_.from = g ._≅_.from ∙ f ._≅_.from
    Iso-Comp ._∙_ f g ._≅_.inverses .Adjoint.η =
      sym ((iso→retract f ∙ iso→retract g) ._Retract-of_.retract-cell)
    Iso-Comp ._∙_ f g ._≅_.inverses .Adjoint.ε =
      (iso→retract⁻ g ∙ iso→retract⁻ f) ._Retract-of_.retract-cell
    Iso-Comp ._∙_ f g ._≅_.inverses .Adjoint.zig = _
    Iso-Comp ._∙_ f g ._≅_.inverses .Adjoint.zag = _

{-# INCOHERENT
  Iso-Refl Iso-Symmetry Iso-Comp
  Iso-Dual
#-}

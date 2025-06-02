{-# OPTIONS --safe #-}
module Notation.Invertibility.Quasi where

open import Prim.Data.Unit
open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Displayed.Composition
open import Notation.Displayed.Reflexivity
open import Notation.Displayed.Symmetry
open import Notation.Displayed.Wide
open import Notation.Duality
open import Notation.Idempotent
open import Notation.Invertibility.Retraction
open import Notation.Invertibility.Section
open import Notation.Reflexivity
open import Notation.Split
open import Notation.Strict
open import Notation.Symmetry
open import Notation.Unitality.Outer

open import Notation.Invertibility.Quasi.Base public

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  Quasi-inversesᵈ : Quiver-onᵈ C (λ _ → ⊤) (λ ℓx ℓy → ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓy ℓy)
  Quasi-inversesᵈ .Quiver-onᵈ.Hom[_] f _ _ = Quasi-inverse f

  infix 10 _≅_
  _≅_ : ∀ {ℓx ℓy} (x : Ob ℓx) (y : Ob ℓy) → Type (ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓy ℓy)
  x ≅ y = Total-hom C Quasi-inversesᵈ {x = x} {y = y} tt tt

  Isos = Wide Quasi-inversesᵈ

  open Quasi-inverse

  instance
    Iso-Sym : Symmetryω Isos
    Iso-Sym .sym e .hom = e .preserves .from
    Iso-Sym .sym e .preserves .from = e .hom
    Iso-Sym .sym e .preserves .to-from = e .preserves .from-to
    Iso-Sym .sym e .preserves .from-to = e .preserves .to-from

    Iso-Dual : Dualω Isos Strict
    Iso-Dual .invol e _ .hom = e .hom
    Iso-Dual .invol e _ .preserves .from = e .preserves .from
    Iso-Dual .invol e _ .preserves .to-from = e .preserves .to-from
    Iso-Dual .invol e _ .preserves .from-to = e .preserves .from-to

  iso→retract : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} → x ≅ y → x Retract-of y
  iso→retract e .hom = e .hom
  iso→retract e .preserves .retraction = e .preserves .from
  iso→retract e .preserves .retraction-cell = e .preserves .to-from

  iso→retract⁻ : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} → x ≅ y → y Retract-of x
  iso→retract⁻ e = iso→retract (e ᵒᵖ)

  open Wide-gpd
  instance
    Quasi-inverse-Reflᵈ : ⦃ _ : ∀{ℓ} {x : Ob ℓ} → Idem C Strict {x = x} refl ⦄
                        → Reflᵈω C Quasi-inversesᵈ
    Quasi-inverse-Reflᵈ .reflᵈ .from = refl
    Quasi-inverse-Reflᵈ .reflᵈ .to-from = idem
    Quasi-inverse-Reflᵈ .reflᵈ .from-to = idem

    Quasi-inverse-Compᵈ : ⦃ _ : Assocω C Strict ⦄ ⦃ _ : Unit-oω C Strict ⦄
                        → Compᵈω C Quasi-inversesᵈ
    Quasi-inverse-Compᵈ ._∙ᵈ_ f′ g′ .from = g′ .from ∙ f′ .from
    Quasi-inverse-Compᵈ ._∙ᵈ_ f′ g′ .to-from =
      (iso→retract (total-hom _ f′) ∙ iso→retract (total-hom _ g′)) .preserves .retraction-cell
    Quasi-inverse-Compᵈ ._∙ᵈ_ f′ g′ .from-to =
      (iso→retract⁻ (total-hom _ g′) ∙ iso→retract⁻ (total-hom _ f′)) .preserves .retraction-cell

{-# DISPLAY Total-hom {_} {_} {_} _ {_} {_} {_} Quasi-inversesᵈ {_} {_} {x} {y} _ _ = x ≅ y #-}

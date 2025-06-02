{-# OPTIONS --safe #-}
module Notation.Invertible.Quasi where

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
open import Notation.Invertible.Quasi.Base public
open import Notation.Invertible.Retraction
open import Notation.Reflexivity
open import Notation.Symmetry
open import Notation.Unitality.Outer
open import Notation.Whiskering.Left
open import Notation.Whiskering.Right

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  Weak-quasi-inversesᵈ : Quiver-onᵈ C (λ _ → ⊤) (λ ℓx ℓy → ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓy ℓy)
  Weak-quasi-inversesᵈ .Quiver-onᵈ.Hom[_] f _ _ = Weak-quasi-inverse C C₂ f

  Weak-iso : ∀{ℓx ℓy} (x : Ob ℓx) (y : Ob ℓy) → Type (ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓy ℓy)
  Weak-iso x y = Total-hom C Weak-quasi-inversesᵈ {x = x} {y = y} tt tt

  Weak-isos : Quiver-on Ob _
  Weak-isos = Wide Weak-quasi-inversesᵈ

  open Weak-quasi-inverse

  iso→iso⁻ : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} → Weak-iso x y → Weak-iso y x
  iso→iso⁻ e .hom = e .preserves .from
  iso→iso⁻ e .preserves .from = e .hom
  iso→iso⁻ e .preserves .to-from = e .preserves .from-to
  iso→iso⁻ e .preserves .from-to = e .preserves .to-from

  iso→retract : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} → Weak-iso x y → Weak-retract C C₂ x y
  iso→retract e .hom = e .hom
  iso→retract e .preserves .retraction = e .preserves .from
  iso→retract e .preserves .retraction-cell = e .preserves .to-from

  iso→retract⁻ : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} → Weak-iso x y → Weak-retract C C₂ y x
  iso→retract⁻ e = iso→retract (iso→iso⁻ e)


module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  {C : Quiver-on Ob ℓ-hom} (open Quiver-on C) {C₂ : 2-Quiver-on C} (open 2-Quiver-on C₂)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where
  open Weak-quasi-inverse
  open Wide-gpd

  instance
    Weak-iso-Sym : Symmetryω (Weak-isos C C₂)
    Weak-iso-Sym .sym = iso→iso⁻ _ _

    Quasi-inverse-Reflᵈ : ⦃ _ : ∀{ℓ} {x : Ob ℓ} → Weak-Idem C C₂ {x = x} refl ⦄
                        → Reflᵈω C (Weak-quasi-inversesᵈ C C₂)
    Quasi-inverse-Reflᵈ .reflᵈ .from = refl
    Quasi-inverse-Reflᵈ .reflᵈ .to-from = idem
    Quasi-inverse-Reflᵈ .reflᵈ .from-to = idem

    Quasi-inverse-Compᵈ : ⦃ _ : Assocω C C₂ ⦄ ⦃ _ : Unit-oω C C₂ ⦄
                          ⦃ _ : Symmetryω₂ C C₂ ⦄ ⦃ _ : Compω₂ C C₂ ⦄ ⦃ _ : Whisker-lω C C₂ ⦄ ⦃ _ : Whisker-rω C C₂ ⦄
                        → Compᵈω C (Weak-quasi-inversesᵈ C C₂)
    Quasi-inverse-Compᵈ ._∙ᵈ_ f′ g′ .from = g′ .from ∙ f′ .from
    Quasi-inverse-Compᵈ ._∙ᵈ_ f′ g′ .to-from = (iso→retract _ _ (total-hom _ f′) ∙ iso→retract _ _ (total-hom _ g′)) .preserves .retraction-cell
    Quasi-inverse-Compᵈ ._∙ᵈ_ f′ g′ .from-to = (iso→retract⁻ _ _ (total-hom _ g′) ∙ iso→retract⁻ _ _ (total-hom _ f′)) .preserves .retraction-cell
    {-# OVERLAPPING Weak-iso-Sym Quasi-inverse-Reflᵈ Quasi-inverse-Compᵈ #-}

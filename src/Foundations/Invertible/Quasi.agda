{-# OPTIONS --safe #-}
module Foundations.Invertible.Quasi where

open import Prim.Data.Unit
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Displayed.Total
open import Notation.Displayed.Wide
open import Notation.Duality
open import Notation.Invertible.Quasi public
open import Notation.Reflexivity

open import Foundations.Path.Groupoid.Base

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  Quasi-inverse : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (to : Hom x y) → Type (ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓy ℓy)
  Quasi-inverse = Weak-quasi-inverse C Strictω

  Quasi-inversesᵈ : Quiver-onᵈ C (λ _ → ⊤) (λ ℓx ℓy → ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓy ℓy)
  Quasi-inversesᵈ = Weak-quasi-inversesᵈ C Strictω

  Isos : Quiver-on Ob _
  Isos = Weak-isos C Strictω

  open Weak-quasi-inverse

  instance
    Iso-Dual : Dualω Isos Strictω
    Iso-Dual .invol e _ .hom = e .hom
    Iso-Dual .invol e _ .preserves .from = e .preserves .from
    Iso-Dual .invol e _ .preserves .to-from = e .preserves .to-from
    Iso-Dual .invol e _ .preserves .from-to = e .preserves .from-to
    {-# OVERLAPPING Iso-Dual #-}

  infix 10 _≅_
  _≅_ Iso : ∀ {ℓx ℓy} (x : Ob ℓx) (y : Ob ℓy) → Type (ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓy ℓy)
  _≅_ = Weak-iso C Strictω
  Iso = _≅_

{-# DISPLAY Weak-quasi-inverse _ Strictω = Quasi-inverse #-}
{-# DISPLAY Total-hom {_} {_} {_} _ {_} {_} {_} (Weak-quasi-inversesᵈ _ Strictω) {_} {_} {x} {y} _ _ = x ≅ y #-}

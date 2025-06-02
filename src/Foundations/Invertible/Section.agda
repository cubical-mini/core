{-# OPTIONS --safe #-}
module Foundations.Invertible.Section where

open import Prim.Data.Unit
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Invertible.Section
  public
open import Notation.Reflexivity

open import Foundations.Idempotent
open import Foundations.Path.Groupoid.Base

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  Split-epi : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (r : Hom y x) → Type (ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓx ℓy)
  Split-epi = Weak-split-epi C Strict

  Split-episᵈ : Quiver-onᵈ C (λ _ → ⊤) _
  Split-episᵈ = Weak-split-episᵈ C Strict

  infix 10 _↠!_
  _↠!_ : ∀ {ℓx ℓy} (y : Ob ℓy) (x : Ob ℓx) → Type (ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓx ℓx)
  y ↠! x = Total-hom C Split-episᵈ {x = y} {y = x} tt tt

  Split-epis : Quiver-on Ob _
  Split-epis = Weak-split-epis C Strict

{-# DISPLAY Weak-split-epi _ Strict = Split-epi #-}
{-# DISPLAY Total-hom {_} {_} {_} _ {_} {_} {_} (Weak-split-episᵈ _ Strict) {_} {_} {x} {y} _ _ = x ↠! y #-}

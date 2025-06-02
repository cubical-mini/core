{-# OPTIONS --safe #-}
module Foundations.Invertible.Retraction where

open import Prim.Data.Unit
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Invertible.Retraction public
open import Notation.Reflexivity

open import Foundations.Path.Groupoid.Base

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  Split-mono : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (s : Hom y x) → Type (ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓy ℓy)
  Split-mono = Weak-split-mono C Strict

  Split-monosᵈ : Quiver-onᵈ C (λ _ → ⊤) _
  Split-monosᵈ = Weak-split-monosᵈ C Strict

  infix 10 _↣!_
  _↣!_ _Retract-of_ : ∀ {ℓx ℓy}(y : Ob ℓy) (x : Ob ℓx) → Type (ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓy ℓy)
  _↣!_ = Weak-retract C Strict
  _Retract-of_ = _↣!_

  Split-monos Retracts : Quiver-on Ob _
  Split-monos = Weak-split-monos C Strict
  Retracts = Split-monos

{-# DISPLAY Weak-split-mono _ Strict = Split-mono #-}
{-# DISPLAY Total-hom {_} {_} {_} _ {_} {_} {_} (Weak-split-monosᵈ _ Strict) {_} {_} {x} {y} _ _ = x ↣! y #-}

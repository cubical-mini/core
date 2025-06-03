{-# OPTIONS --safe #-}
module Notation.Reflexivity where

open import Prim.Type

open import Notation.Base

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) where

  record Refl ℓ : Type (ℓ-ob ℓ l⊔ ℓ-hom ℓ ℓ) where
    no-eta-equality
    field refl : {x : Ob ℓ} → Hom x x

  Reflω : Typeω
  Reflω = {ℓ : Level} → Refl ℓ

open Refl ⦃ ... ⦄ public

{-# DISPLAY Refl.refl _ = refl #-}

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C  : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  where
  Refl₂ : (ℓx ℓy : Level) → Type (ℓ-ob ℓx l⊔ ℓ-ob ℓy l⊔ ℓ-hom ℓx ℓy)
  Refl₂ ℓx ℓy = {x : Ob ℓx} {y : Ob ℓy} → Refl (Quiver₂ x y) ℓx

  Reflω₂ : Typeω
  Reflω₂ = ∀{ℓx ℓy} → Refl₂ ℓx ℓy

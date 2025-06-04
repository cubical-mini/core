{-# OPTIONS --safe #-}
module Notation.Displayed.Total.Base where

open import Prim.Type

open import Notation.Base
open import Notation.Displayed.Base

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  {ℓ-obᵈ : ℓ-ob-sig} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ} {ℓ-homᵈ : ℓ-hom-sig} (D : Quiver-onᵈ C Ob[_] ℓ-homᵈ) (open Quiver-onᵈ D)
  {ℓx : Level} where

  record Total-ob : Type (ℓ-ob ℓx l⊔ ℓ-obᵈ ℓx) where
    constructor total-ob
    field
      carrier    : Ob ℓx
      structured : Ob[ carrier ]

  module _ {ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (x′ : Ob[ x ]) (y′ : Ob[ y ]) where
    record Total-hom : Type (ℓ-hom ℓx ℓy l⊔ ℓ-homᵈ ℓx ℓy) where
      constructor total-hom
      field
        hom       : Hom x y
        preserves : Hom[ hom ] x′ y′

open Total-ob  public
open Total-hom public

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓ-obᵈ : ℓ-ob-sig} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ} {ℓ-homᵈ : ℓ-hom-sig} (D : Quiver-onᵈ C Ob[_] ℓ-homᵈ) (open Quiver-onᵈ D) where

  ∫ : Quiver-on (λ ℓ → Total-ob C D {ℓx = ℓ}) _
  ∫ .Quiver-on.Hom x′ y′ = Total-hom C D (x′ .structured) (y′ .structured)

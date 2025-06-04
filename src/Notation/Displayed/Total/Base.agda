{-# OPTIONS --safe #-}
module Notation.Displayed.Total.Base where

open import Prim.Type

open import Notation.Base
open import Notation.Displayed.Base

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  {ℓ-obᵈ : ℓ-ob-sig} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ) where

  record Total-ob ℓ : Type (ℓ-ob ℓ l⊔ ℓ-obᵈ ℓ) where
    constructor total-ob
    field
      carrier    : Ob ℓ
      structured : Ob[ carrier ]

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  {ℓ-obᵈ : ℓ-ob-sig} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ} {ℓ-homᵈ : ℓ-hom-sig} (D : Quiver-onᵈ C Ob[_] ℓ-homᵈ) (open Quiver-onᵈ D)
  {ℓx : Level} {ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} where

  record Total-hom (x′ : Ob[ x ]) (y′ : Ob[ y ]) : Type (ℓ-hom ℓx ℓy l⊔ ℓ-homᵈ ℓx ℓy) where
    constructor total-hom
    field
      hom       : Hom x y
      preserves : Hom[ hom ] x′ y′

open Total-ob  public
open Total-hom public

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓ-obᵈ : ℓ-ob-sig} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ} {ℓ-homᵈ : ℓ-hom-sig} (D : Quiver-onᵈ C Ob[_] ℓ-homᵈ) (open Quiver-onᵈ D) where

  ∫ : Quiver-on (Total-ob C Ob[_]) _
  ∫ .Quiver-on.Hom x′ y′ = Total-hom C D (x′ .structured) (y′ .structured)

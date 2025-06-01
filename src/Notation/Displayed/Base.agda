{-# OPTIONS --safe #-}
module Notation.Displayed.Base where

open import Prim.Type

open import Notation.Base

ob-sigᵈ : {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) (ℓ-obᵈ : ℓ-ob-sig) → Typeω
ob-sigᵈ Ob ℓ-obᵈ = {ℓ : Level} → Ob ℓ → Type (ℓ-obᵈ ℓ)
{-# INLINE ob-sigᵈ #-}

hom-sigᵈ
  : {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) {ℓ-hom : ℓ-hom-sig} (Hom : hom-sig Ob ℓ-hom)
    {ℓ-obᵈ : ℓ-ob-sig} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ) (ℓ-homᵈ : ℓ-hom-sig)
  → Typeω
hom-sigᵈ Ob Hom Ob[_] ℓ-homᵈ = {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} → Hom x y → Ob[ x ] → Ob[ y ] → Type (ℓ-homᵈ ℓx ℓy)
{-# INLINE hom-sigᵈ #-}

record Quiver-onᵈ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom)
  {ℓ-obᵈ : ℓ-ob-sig} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ) (ℓ-homᵈ : ℓ-hom-sig) : Typeω where
  constructor mk-quiverᵈ
  no-eta-equality
  open Quiver-on C
  field Hom[_] : hom-sigᵈ Ob Hom Ob[_] ℓ-homᵈ
{-# INLINE mk-quiverᵈ #-}


module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  {ℓ-obᵈ : ℓ-ob-sig} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ} {ℓ-homᵈ : ℓ-hom-sig} (D : Quiver-onᵈ C Ob[_] ℓ-homᵈ) (open Quiver-onᵈ D)
  {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (x′ : Ob[ x ]) (y′ : Ob[ y ]) where

  record Total-hom : Type (ℓ-hom ℓx ℓy l⊔ ℓ-homᵈ ℓx ℓy) where
    constructor total-hom
    field
      hom       : Hom x y
      preserves : Hom[ hom ] x′ y′

open Total-hom public

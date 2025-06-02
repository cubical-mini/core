{-# OPTIONS --safe #-}
module Notation.Base where

open import Prim.Type

ℓ-ob-sig = Level → Level
ℓ-hom-sig = Level → Level → Level

ob-sig : (ℓ-ob : ℓ-ob-sig) → Typeω
ob-sig ℓ-ob = ∀ ℓ → Type (ℓ-ob ℓ)
{-# INLINE ob-sig #-}

hom-sig : {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) (ℓ-hom : ℓ-hom-sig) → Typeω
hom-sig Ob ℓ-hom = ∀{ℓx ℓy} → Ob ℓx → Ob ℓy → Type (ℓ-hom ℓx ℓy)
{-# INLINE hom-sig #-}

record Quiver-on {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) (ℓ-hom : ℓ-hom-sig) : Typeω where
  constructor mk-quiver
  no-eta-equality
  field Hom : hom-sig Ob ℓ-hom
{-# INLINE mk-quiver #-}

_ᵒᵖω : {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} → Quiver-on Ob ℓ-hom → Quiver-on Ob (λ ℓx ℓy → ℓ-hom ℓy ℓx)
(C ᵒᵖω) .Quiver-on.Hom x y = Hom y x where open Quiver-on C


-- Strict 2-quivers

-- globular vibe
2-hom-sig : {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) {ℓ-hom : ℓ-hom-sig} (Hom : hom-sig Ob ℓ-hom) → Typeω
2-hom-sig Ob {ℓ-hom} Hom = ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (f g : Hom x y) → Type (ℓ-hom ℓx ℓy)
{-# INLINE 2-hom-sig #-}

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) where
  record 2-Quiver-on : Typeω where
    constructor mk-2-quiver
    no-eta-equality
    field Quiver₂ : ∀{ℓx ℓy} (x : Ob ℓx) (y : Ob ℓy) → Quiver-on (λ _ → Hom x y) (λ _ _ → ℓ-hom ℓx ℓy)

    2-Hom : 2-hom-sig Ob Hom
    2-Hom {ℓx} {ℓy} {x} {y} = Quiver-on.Hom (Quiver₂ x y) {ℓx} {ℓx} -- TODO no idea what's going on
{-# INLINE mk-2-quiver #-}

_²ᵒᵖω : {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (CC : 2-Quiver-on C) → 2-Quiver-on C
_²ᵒᵖω CC .2-Quiver-on.Quiver₂ x y = CC .2-Quiver-on.Quiver₂ x y ᵒᵖω

{-# OPTIONS --safe #-}
module Notation.Quiver where

open import Prim.Type

ℓ-ob-sig = Level → Level
ℓ-hom-sig = Level → Level → Level

ob-sig : (ℓ-ob : ℓ-ob-sig) → Typeω
ob-sig ℓ-ob = (ℓ : Level) → Type (ℓ-ob ℓ)
{-# INLINE ob-sig #-}

hom-sig : {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) (ℓ-hom : ℓ-hom-sig) → Typeω
hom-sig Ob ℓ-hom = {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (ℓ-hom ℓx ℓy)
{-# INLINE hom-sig #-}

record Quiver-on {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) : Typeω where
  constructor mk-quiver
  no-eta-equality
  field
    {ℓ-hom} : ℓ-hom-sig
    Hom     : hom-sig Ob ℓ-hom

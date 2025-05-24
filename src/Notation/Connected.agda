{-# OPTIONS --safe #-}
module Notation.Connected where

open import Prim.Type

open import Notation.Base

-- coherent, can be used for instance resolution
module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (CC : 2-Quiver-on C) (open 2-Quiver-on CC) where

  record Connected ℓ ℓ′ : Type (ℓ-ob ℓ l⊔ ℓ-ob ℓ′ l⊔ ℓ-hom ℓ ℓ′) where
    no-eta-equality
    constructor mk-connected
    field
      centre      : {x : Ob ℓ} {y : Ob ℓ′} → Hom x y
      centre-cell : {x : Ob ℓ} {y : Ob ℓ′} (f : Hom x y) → 2-Hom centre f

open Connected ⦃ ... ⦄ public
  using (centre ; centre-cell)

{-# DISPLAY Connected.centre _ = centre #-}
{-# DISPLAY Connected.centre-cell _ = centre-cell #-}

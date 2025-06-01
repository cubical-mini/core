{-# OPTIONS --safe #-}
module Notation.Thin where

open import Prim.Type

open import Notation.Base

-- coherent when strict, can be used for instance resolution
module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (CC : 2-Quiver-on C) (open 2-Quiver-on CC) where

  record Thin ℓ ℓ′ : Type (ℓ-ob ℓ l⊔ ℓ-ob ℓ′ l⊔ ℓ-hom ℓ ℓ′) where
    no-eta-equality
    constructor mk-thin
    field thin-cell : {x : Ob ℓ} {y : Ob ℓ′} (f g : Hom x y) → 2-Hom f g

open Thin public

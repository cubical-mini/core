{-# OPTIONS --safe #-}
module Notation.Initial where

open import Prim.Type

open import Notation.Base

-- coherent when strict, can be used for instance resolution
module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (CC : 2-Quiver-on C) (open 2-Quiver-on CC) where

  record Initial ℓi ℓ : Type (ℓ-ob ℓi l⊔ ℓ-ob ℓ l⊔ ℓ-hom ℓi ℓ) where
    no-eta-equality
    constructor mk-initial
    field
      ⊥      : Ob ℓi
      ¡      : {x : Ob ℓ} → Hom ⊥ x
      ¡-cell : {x : Ob ℓ} (h : Hom ⊥ x) → 2-Hom ¡ h

open Initial ⦃ ... ⦄ public
  using (⊥ ; ¡ ; ¡-cell)

{-# DISPLAY Initial.⊥ _ = ⊥ #-}
{-# DISPLAY Initial.¡ _ = ¡ #-}
{-# DISPLAY Initial.¡-cell _ h = ¡-cell h #-}

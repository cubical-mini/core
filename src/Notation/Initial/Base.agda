{-# OPTIONS --safe #-}
module Notation.Initial.Base where

open import Prim.Type

open import Notation.Base

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  where

  record Weak-Initial ℓi ℓ : Type (ℓ-ob ℓi l⊔ ℓ-ob ℓ l⊔ ℓ-hom ℓi ℓ) where
    no-eta-equality
    constructor mk-initial
    field
      ⊥      : Ob ℓi
      ¡      : {x : Ob ℓ} → Hom ⊥ x
      ¡-cell : {x : Ob ℓ} (h : Hom ⊥ x) → 2-Hom ¡ h

open Weak-Initial ⦃ ... ⦄ public
  using (⊥ ; ¡ ; ¡-cell)

{-# DISPLAY Weak-Initial.⊥ _ = ⊥ #-}
{-# DISPLAY Weak-Initial.¡ _ = ¡ #-}
{-# DISPLAY Weak-Initial.¡-cell _ h = ¡-cell h #-}

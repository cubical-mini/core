{-# OPTIONS --safe --erased-cubical #-}
module Notation.Univalent where

open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Refl.Base

module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom : ℓ-sig²}
  (C : Quiverω ℓ-ob ℓ-hom) (open Quiverω C) ⦃ _ : Reflω C ⦄ where

  record Univalent ℓ : Typeω where
    no-eta-equality
    field
      to-path : {x y : Ob ℓ} → Hom x y → x ＝ y
      to-path-over : {x y : Ob ℓ} (p : Hom x y)
                   → Pathᴾ (λ i → Hom x (to-path p i)) refl p

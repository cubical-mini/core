{-# OPTIONS --safe #-}
module Notation.Idempotence where

open import Prim.Kan
open import Prim.Type

open import Notation.Composition
open import Notation.Quiver

module _ {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob)
  {ℓ-hom : ℓ-hom-sig} (Hom : hom-sig Ob ℓ-hom) ⦃ _ : Comp Ob Hom ⦄
  (_~_ : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (f g : Hom x y) → Type (ℓ-hom ℓx ℓy)) where

  record Idem : Typeω where
    no-eta-equality
    field idem : {ℓ : Level} {x : Ob ℓ} (e : Hom x x)
               → e ∙ e ~ e

open Idem ⦃ ... ⦄ public

{-# DISPLAY Idem.idem _ e = idem e #-}

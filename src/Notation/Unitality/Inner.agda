{-# OPTIONS --safe #-}
module Notation.Unitality.Inner where

open import Prim.Kan
open import Prim.Type

open import Notation.Composition
open import Notation.Quiver
open import Notation.Reflexivity

module _ {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob)
  {ℓ-hom : ℓ-hom-sig} (Hom : hom-sig Ob ℓ-hom) ⦃ _ : Refl Ob Hom ⦄ ⦃ _ : Comp Ob Hom ⦄
  (_~_ : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (f g : Hom x y) → Type (ℓ-hom ℓx ℓy)) where

  record Unit-i : Typeω where
    no-eta-equality
    field ∙-id-i : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (f : Hom x y)
                 → refl ∙ f ~ f

open Unit-i ⦃ ... ⦄ public

{-# DISPLAY Unit-i.∙-id-i _ f = ∙-id-i f #-}

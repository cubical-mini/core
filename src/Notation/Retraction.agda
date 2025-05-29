{-# OPTIONS --safe #-}
module Notation.Retraction where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (CC : 2-Quiver-on C) (open 2-Quiver-on CC) where

  module _ {ℓx ℓy : Level} ⦃ _ : Refl C ℓy ⦄ ⦃ _ : Comp C ℓy ℓx ℓy ⦄ where
    Weak-retraction : {x : Ob ℓx} {y : Ob ℓy} (r : Hom x y) (s : Hom y x) → Type (ℓ-hom ℓy ℓy)
    Weak-retraction r s = 2-Hom (s ∙ r) refl

  module _ {ℓx ℓy : Level} ⦃ _ : Refl C ℓx ⦄ ⦃ _ : Comp C ℓx ℓy ℓx ⦄ where
    record Weak-split-mono {x : Ob ℓx} {y : Ob ℓy} (s : Hom x y) : Type (ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓy ℓx) where
      no-eta-equality
      field
        retraction      : Hom y x
        retraction-cell : Weak-retraction retraction s

open Weak-split-mono ⦃ ... ⦄ public
  using (retraction-cell)

{-# DISPLAY Weak-split-mono.retraction-cell _ = retraction-cell #-}

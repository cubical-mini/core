{-# OPTIONS --safe #-}
module Notation.Split.Base where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  Splitting : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (s : Hom y x) (r : Hom x y) → Type (ℓ-hom ℓy ℓy)
  Splitting s r = 2-Hom (s ∙ r) refl
  {-# INLINE Splitting #-}

  record Weak-Split {ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (s : Hom y x) (r : Hom x y) : Type (ℓ-hom ℓy ℓy) where
    no-eta-equality
    field split : Splitting s r

open Weak-Split ⦃ ... ⦄ public

{-# DISPLAY Weak-Split.split _ = split #-}

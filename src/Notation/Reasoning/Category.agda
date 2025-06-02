{-# OPTIONS --safe #-}
module Notation.Reasoning.Category where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reasoning.Semicategory
open import Notation.Reflexivity
open import Notation.Unitality.Inner
open import Notation.Unitality.Outer
open import Notation.Whiskering.Left
open import Notation.Whiskering.Right

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  {C : Quiver-on Ob ℓ-hom} (open Quiver-on C) {C₂ : 2-Quiver-on C} (open 2-Quiver-on C₂)
  ⦃ _ : Compω C ⦄ ⦃ _ : Reflω C ⦄
  ⦃ _ : Compω₂ C C₂ ⦄ where

  module _ {ℓw ℓx ℓy ℓz}
           {w : Ob ℓw} {x : Ob ℓx} {y : Ob ℓy} {z : Ob ℓz}
           {f : Hom w x} {s : Hom x y} {r : Hom y x} {g : Hom x z} where

    module _ ⦃ _ : Whisker-lω C C₂ ⦄ ⦃ _ : Whisker-rω C C₂ ⦄ where
      collapse-l : ⦃ _ : Unit-oω C C₂ ⦄
                 → 2-Hom (s ∙ r) refl
                 → 2-Hom ((f ∙ (s ∙ r)) ∙ g) (f ∙ g)
      collapse-l prf = (f ◁ prf) ∙ id-o f ▷ g

      collapse-r : ⦃ _ : Unit-iω C C₂ ⦄
                 → 2-Hom (s ∙ r) refl
                 → 2-Hom (f ∙ ((s ∙ r) ∙ g)) (f ∙ g)
      collapse-r prf = f ◁ (prf ▷ g) ∙ id-i g

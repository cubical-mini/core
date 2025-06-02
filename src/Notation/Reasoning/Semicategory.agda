{-# OPTIONS --safe #-}
module Notation.Reasoning.Semicategory where

open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Symmetry
open import Notation.Whiskering.Right

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  {C : Quiver-on Ob ℓ-hom} (open Quiver-on C) {C₂ : 2-Quiver-on C} (open 2-Quiver-on C₂)
  ⦃ _ : Compω C ⦄ ⦃ _ : Assocω C C₂ ⦄
  ⦃ _ : Compω₂ C C₂ ⦄ where

  module _ {ℓu ℓw ℓx ℓy ℓz}
           {u : Ob ℓu} {w : Ob ℓw} {x : Ob ℓx} {y : Ob ℓy} {z : Ob ℓz}
           {f : Hom u w} {g : Hom w x} {h : Hom x y} {k : Hom y z} where

    assoc-l : 2-Hom (f ∙ (g ∙ (h ∙ k))) (((f ∙ g) ∙ h) ∙ k)
    assoc-l = assoc f g (h ∙ k) ∙ assoc (f ∙ g) h k

    module _ ⦃ _ : Symmetryω₂ C C₂ ⦄ where
      assoc-r : 2-Hom (((f ∙ g) ∙ h) ∙ k) (f ∙ (g ∙ (h ∙ k)))
      assoc-r = sym assoc-l

      module _ ⦃ _ : Whisker-rω C C₂ ⦄  where
        centralize : 2-Hom ((f ∙ g) ∙ (h ∙ k)) (f ∙ (g ∙ h) ∙ k)
        centralize = assoc (f ∙ g) h k ∙ sym (assoc f g h ▷ k)

        disperse : 2-Hom (f ∙ (g ∙ h) ∙ k) ((f ∙ g) ∙ (h ∙ k))
        disperse = sym centralize

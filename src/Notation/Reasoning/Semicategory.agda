{-# OPTIONS --safe #-}
module Notation.Reasoning.Semicategory where

open import Prim.Kan
open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Strict
open import Notation.Whiskering.Right

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  {C : Quiver-on Ob ℓ-hom} (open Quiver-on C) {C₂ : 2-Quiver-on C} (open 2-Quiver-on C₂)
  ⦃ _ : Compω C ⦄ ⦃ _ : Assocω C C₂ ⦄ ⦃ _ : Assocω C (C₂ ²ᵒᵖω) ⦄
  ⦃ _ : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} → Compω (Quiver₂ x y) ⦄ where

  module _ {ℓu ℓw ℓx ℓy ℓz}
           {u : Ob ℓu} {w : Ob ℓw} {x : Ob ℓx} {y : Ob ℓy} {z : Ob ℓz}
           {f : Hom u w} {g : Hom w x} {h : Hom x y} {k : Hom y z} where

    assoc-l : 2-Hom (f ∙ (g ∙ (h ∙ k))) (((f ∙ g) ∙ h) ∙ k)
    assoc-l = assoc f g (h ∙ k) ∙ assoc (f ∙ g) h k

    assoc-r : 2-Hom (((f ∙ g) ∙ h) ∙ k) (f ∙ (g ∙ (h ∙ k)))
    assoc-r = assoc (f ∙ g) h k ∙ assoc f g (h ∙ k)

    module _ ⦃ _ : Whisker-rω C C₂ ⦄  where
      centralize : 2-Hom ((f ∙ g) ∙ (h ∙ k)) (f ∙ (g ∙ h) ∙ k)
      centralize = assoc (f ∙ g) h k ∙ (assoc f g h ▷ k)

      disperse : 2-Hom (f ∙ (g ∙ h) ∙ k) ((f ∙ g) ∙ (h ∙ k))
      disperse = (assoc f g h ▷ k) ∙ assoc (f ∙ g) h k

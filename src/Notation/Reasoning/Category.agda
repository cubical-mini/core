{-# OPTIONS --safe #-}
module Notation.Reasoning.Category where

open import Prim.Kan
open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Reasoning.Semicategory
open import Notation.Reflexivity
open import Notation.Split
open import Notation.Strict
open import Notation.Unitality.Outer
open import Notation.Whiskering.Left
open import Notation.Whiskering.Right

open import Foundations.Path.Base
  using ()
  renaming (_∙_ to _∙ₚ_)

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Compω C ⦄ ⦃ _ : Reflω C ⦄ ⦃ _ : ∀{ℓx ℓy} → Unit-o C Strict ℓx ℓy ⦄ where

  module _ {ℓw ℓx ℓy ℓz : Level}
           {w : Ob ℓw} {x : Ob ℓx} {y : Ob ℓy} {z : Ob ℓz}
           {f : Hom w x} {s : Hom x y} {r : Hom y x} {g : Hom x z} where

    collapse : s ∙ r ＝ refl
             → f ∙ (s ∙ r) ∙ g ＝ f ∙ g
    collapse prf = ((f ◁ prf) ▷ g) ∙ₚ (id-o f ▷ g)

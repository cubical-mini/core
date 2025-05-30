{-# OPTIONS --safe #-}
module Notation.Empty where

open import Prim.Data.Empty
open import Prim.Type

open import Notation.Base

Empty : {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) (ℓ-hom : ℓ-hom-sig) → Quiver-on Ob ℓ-hom
Empty _ ℓ-hom .Quiver-on.Hom {ℓx} {ℓy} _ _ = Lift (ℓ-hom ℓx ℓy) ⊥

2-Empty : {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom}
        → 2-Quiver-on C
2-Empty {C} .2-Quiver-on.Quiver₂ x y = Empty (λ _ → Hom x y) _ where open Quiver-on C

3-Empty : {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} {C₂ : 2-Quiver-on C}
        → 3-Quiver-on C C₂
3-Empty {C₂} .3-Quiver-on.Quiver₃ f g = Empty (λ _ → 2-Hom f g) _ where open 2-Quiver-on C₂

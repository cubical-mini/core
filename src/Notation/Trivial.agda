{-# OPTIONS --safe #-}
module Notation.Trivial where

open import Prim.Data.Unit
open import Prim.Type

open import Notation.Base

Trivial : {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) (ℓ-hom : ℓ-hom-sig) → Quiver-on Ob ℓ-hom
Trivial _ ℓ-hom .Quiver-on.Hom {ℓx} {ℓy} _ _ = Lift (ℓ-hom ℓx ℓy) ⊤

2-Trivial : {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom}
          → 2-Quiver-on C
2-Trivial {C} .2-Quiver-on.Quiver₂ x y = Trivial (λ _ → Hom x y) _ where open Quiver-on C

3-Trivial : {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} {C₂ : 2-Quiver-on C}
          → 3-Quiver-on C C₂
3-Trivial {C₂} .3-Quiver-on.Quiver₃ f g = Trivial (λ _ → 2-Hom f g) _ where open 2-Quiver-on C₂

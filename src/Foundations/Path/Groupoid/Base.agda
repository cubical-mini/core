{-# OPTIONS --safe #-}
module Foundations.Path.Groupoid.Base where

open import Prim.Kan
open import Prim.Type

open import Notation.Base

Paths : ∀{ℓ} (A : Type ℓ) → Quiver-on (λ _ → A) _
Paths A .Quiver-on.Hom = Path A

Strict : {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom}
       → 2-Quiver-on C
Strict {C} .2-Quiver-on.Quiver₂ x y = Paths (Hom x y) where open Quiver-on C

2-Strict : {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} {C₂ : 2-Quiver-on C}
         → 3-Quiver-on C C₂
2-Strict {C₂} .3-Quiver-on.Quiver₃ f g = Paths (2-Hom f g) where open 2-Quiver-on C₂

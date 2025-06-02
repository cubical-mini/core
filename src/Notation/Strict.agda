{-# OPTIONS --safe #-}
module Notation.Strict where

open import Prim.Kan
open import Prim.Type

open import Notation.Base

Paths : ∀{ℓ} (A : Type ℓ) → Quiver-on (λ _ → A) _
Paths A .Quiver-on.Hom = Path A

Strict : {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom}
       → 2-Quiver-on C
Strict {C} .2-Quiver-on.Quiver₂ x y = Paths (Hom x y) where open Quiver-on C

-- TODO
-- Squares : {ℓ : Level} (A : Type ℓ) → ℚuiver-on (λ _ → A) _
-- Squares A .ℚuiver-on.Quiverₕ = Paths A
-- Squares A .ℚuiver-on.Quiverᵥ = Paths A
-- Squares A .ℚuiver-on.Sq      = Squareₚ

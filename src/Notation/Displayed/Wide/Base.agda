{-# OPTIONS --safe #-}
module Notation.Displayed.Wide.Base where

open import Prim.Data.Unit
open import Prim.Type

open import Notation.Base
open import Notation.Displayed.Base
open import Notation.Displayed.Total

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓ-homᵈ : ℓ-hom-sig} (D : Quiver-onᵈ C (λ {_} _ → ⊤) ℓ-homᵈ) (open Quiver-onᵈ D) where
  Wide : Quiver-on Ob _
  Wide .Quiver-on.Hom x y = Total-hom C D {x = x} {y = y} tt tt

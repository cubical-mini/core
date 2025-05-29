{-# OPTIONS --safe #-}
module Notation.Connected.Strict where

open import Prim.Interval
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Connected
open import Notation.Reflexivity
open import Notation.Strict
open import Notation.Symmetry

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓx ℓy : Level} where instance

  Connected⁻ : ⦃ Co : Connected C Strict ℓx ℓy ⦄ → Connected C (Strict ²ᵒᵖω) ℓx ℓy
  Connected⁻ ⦃ Co ⦄ .centre = centre ⦃ Co ⦄
  Connected⁻ ⦃ Co ⦄ .centre-cell f i = centre-cell ⦃ Co ⦄ f (~ i)
  {-# INCOHERENT Connected⁻ #-}


-- TODO move to tests or doc
module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) where

  funny : {ℓ : Level} → Connected C Strict ℓ ℓ → Refl C ℓ
  funny cc .refl {x} = cc .Connected.centre

  funny2 : {ℓx ℓy : Level} → Connected C Strict ℓy ℓx → Symmetry C ℓx ℓy
  funny2 cc .sym {x} {y} _ = cc .Connected.centre

  hmmmm : {ℓx ℓy ℓz : Level} → Connected C Strict ℓx ℓz → Comp C ℓx ℓy ℓz
  hmmmm cc ._∙_ {x} {z} _ _ = cc .Connected.centre

  -- connected gives trivial groupoid

-- TODO remove
open import Prim.Data.Unit
Trivial : Quiver-on (λ _ → ⊤ₜ) _
Trivial .Quiver-on.Hom _ _ = ⊤ₜ

Conn-Trivial : Connected Trivial Strict lzero lzero
Conn-Trivial .Connected.centre = tt
Conn-Trivial .Connected.centre-cell _ _ = _

open import Prim.Data.Empty
Empty : Quiver-on (λ _ → ⊥ₜ) _
Empty .Quiver-on.Hom _ _ = ⊥ₜ

Conn-Empty : Connected Empty Strict lzero lzero
Conn-Empty .Connected.centre {()}
Conn-Empty .Connected.centre-cell ()

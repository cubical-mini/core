{-# OPTIONS --safe #-}
module Notation.Connected.Strict where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Connected
open import Notation.Reflexivity
open import Notation.Strict
open import Notation.Symmetry

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) where

  funny : {ℓ : Level} → Connected C Strict ℓ ℓ → Refl C ℓ
  funny cc .refl {x} = cc .Connected.conn x x

  funny2 : {ℓx ℓy : Level} → Connected C Strict ℓy ℓx → Symmetry C ℓx ℓy
  funny2 cc .sym {x} {y} _ = cc .Connected.conn y x

  hmmmm : {ℓx ℓy ℓz : Level} → Connected C Strict ℓx ℓz → Comp C ℓx ℓy ℓz
  hmmmm cc ._∙_ {x} {z} _ _ = cc .Connected.conn x z

  -- connected gives trivial groupoid

-- TODO remove
open import Prim.Data.Unit
Trivial : Quiver-on (λ _ → ⊤ₜ) _
Trivial .Quiver-on.Hom _ _ = ⊤ₜ

Conn-Trivial : Connected Trivial Strict lzero lzero
Conn-Trivial .Connected.conn _ _ = tt
Conn-Trivial .Connected.conn-cell _ _ = _

open import Prim.Data.Empty
Empty : Quiver-on (λ _ → ⊥ₜ) _
Empty .Quiver-on.Hom _ _ = ⊥ₜ

Conn-Empty : Connected Empty Strict lzero lzero
Conn-Empty .Connected.conn ()
Conn-Empty .Connected.conn-cell ()

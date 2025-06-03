{-# OPTIONS --safe #-}
module README.Notation.Connected where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Connected
open import Notation.Reflexivity
open import Notation.Strict
open import Notation.Symmetry

-- connected gives trivial groupoid

-- TODO remove
open import Prim.Data.Unit
Trivial : Quiver-on (λ _ → ⊤) _
Trivial .Quiver-on.Hom _ _ = ⊤

Conn-Trivial : Connected Trivial Strict lzero lzero
Conn-Trivial .Connected.centre = tt
Conn-Trivial .Connected.centre-cell _ _ = _

open import Prim.Data.Empty
Empty : Quiver-on (λ _ → ⊥) _
Empty .Quiver-on.Hom _ _ = ⊥

Conn-Empty : Connected Empty Strict lzero lzero
Conn-Empty .Connected.centre {()}
Conn-Empty .Connected.centre-cell ()

{-# OPTIONS --safe #-}
module Notation.Initial.Strict where

-- NB: this is not a strict initial object in nLab sense

open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Connected.Wild
open import Notation.Initial
open import Notation.Initial.Wild
open import Notation.Strict

open import Foundations.HLevel.Base

-- TODO reasoning
module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  {ℓi ℓ : Level} ⦃ _ : Initial C Strict ℓi ℓ ⦄ where

  ¡-unique : {x : Ob ℓ} (h : Hom ⊥ x) → ¡ ＝ h
  ¡-unique = ¡-cell

  ¡-unique² : {x : Ob ℓ} (f g : Hom ⊥ x) → f ＝ g
  ¡-unique² f g = is-contr→is-prop (mk-wild-initial ¡ (¡-unique _)) .Wild-connected.conn f g

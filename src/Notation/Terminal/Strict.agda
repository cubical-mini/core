{-# OPTIONS --safe #-}
module Notation.Terminal.Strict where

open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Strict
open import Notation.Terminal

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  {ℓt ℓ : Level} ⦃ _ : Terminal C Strict ℓt ℓ ⦄ where

  -- reasoning

  -- TODO requires is-contr→is-prop
  -- ¡-unique² : {x : Ob ℓ} (f g : Hom ⊥ x) → f ＝ g
  -- ¡-unique² f g = {!!}

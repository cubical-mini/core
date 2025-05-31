{-# OPTIONS --safe #-}
module Notation.Terminal.Reasoning where

open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Connected
open import Notation.Strict
open import Notation.Terminal
open import Notation.Thin

open import Foundations.HLevel.Base

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓt ℓ : Level} ⦃ _ : Terminal C Strict ℓt ℓ ⦄ where

  !-unique : {x : Ob ℓ} (h : Hom x ⊤) → h ＝ !
  !-unique = !-cell

  !-unique² : {x : Ob ℓ} (f g : Hom x ⊤) → f ＝ g
  !-unique² = is-contr→is-prop (mk-connected ! λ h i → !-unique h (~ i)) .thin-cell

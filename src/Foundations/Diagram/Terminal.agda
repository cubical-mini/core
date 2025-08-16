{-# OPTIONS --safe #-}
module Foundations.Diagram.Terminal where

open import Foundations.Base
open import Foundations.Cubical.HLevel.Base

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-het}
  (C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω C) where

  record Terminal ℓ-ter : Typeω where
    no-eta-equality
    field
      ⊤        : Ob⁺ ℓ-ter
      !        : ∀{ls} {x : Ob⁻ ls} → Het x ⊤
      !-unique : ∀{ls} (x : Ob⁻ ls) → is-central {A = Het x ⊤} !

open Terminal ⦃ ... ⦄ public
  using (⊤ ; ! ; !-unique)
{-# DISPLAY Terminal.⊤ _ = ⊤ #-}
{-# DISPLAY Terminal.! _ = ! #-}
{-# DISPLAY Terminal.!-unique _ x = !-unique x #-}

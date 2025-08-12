{-# OPTIONS --safe #-}
module Foundations.Quiver.Diagram.Terminal where

open import Foundations.HLevel.Base
open import Foundations.Quiver.Base

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-het}
  (C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω C) where

  record Terminal ℓ-ter ls : Type
    (ℓ-ob⁺ ℓ-ter ⊔ ℓ-ob⁻ ls ⊔ ℓ-het ls ℓ-ter) where
    no-eta-equality
    field
      ⊤        : Ob⁺ ℓ-ter
      !        : {x : Ob⁻ ls} → Het x ⊤
      !-unique : (x : Ob⁻ ls) → is-central⁺ (Het x ⊤) !

  Terminalω : ∀ ℓ-ter → Typeω
  Terminalω ℓ-ter = ∀{ls} → Terminal ℓ-ter ls

open Terminal ⦃ ... ⦄ public
  using (⊤ ; ! ; !-unique)
{-# DISPLAY Terminal.⊤ _ = ⊤ #-}
{-# DISPLAY Terminal.! _ = ! #-}
{-# DISPLAY Terminal.!-unique _ x = !-unique x #-}

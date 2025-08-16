{-# OPTIONS --safe #-}
module Foundations.Diagram.Initial where

open import Foundations.Base
open import Foundations.Cubical.HLevel.Base

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-het}
  (C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω C) where

  record Initial ℓ-ini : Typeω where
    no-eta-equality
    field
      ⊥        : Ob⁻ ℓ-ini
      ¡        : ∀{ls} {x : Ob⁺ ls} → Het ⊥ x
      ¡-unique : ∀{ls} (x : Ob⁺ ls) → is-central {A = Het ⊥ x} ¡

open Initial ⦃ ... ⦄ public
  using (⊥ ; ¡ ; ¡-unique)
{-# DISPLAY Initial.⊥ _ = ⊥ #-}
{-# DISPLAY Initial.¡ _ = ¡ #-}
{-# DISPLAY Initial.¡-unique _ x = ¡-unique x #-}

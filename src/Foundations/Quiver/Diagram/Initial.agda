{-# OPTIONS --safe #-}
module Foundations.Quiver.Diagram.Initial where

open import Foundations.HLevel.Base
open import Foundations.Quiver.Base

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-het}
  (C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω C) where

  record Initial ℓ-ini ls : Type
    (ℓ-ob⁻ ℓ-ini ⊔ ℓ-ob⁺ ls ⊔ ℓ-het ℓ-ini ls) where
    no-eta-equality
    field
      ⊥        : Ob⁻ ℓ-ini
      ¡        : {x : Ob⁺ ls} → Het ⊥ x
      ¡-unique : (x : Ob⁺ ls) → is-central⁻ (Het ⊥ x) ¡

  Initialω : ∀ ℓ-ini → Typeω
  Initialω ℓ-ini = ∀{ls} → Initial ℓ-ini ls

open Initial ⦃ ... ⦄ public
  using (⊥ ; ¡ ; ¡-unique)
{-# DISPLAY Initial.⊥ _ = ⊥ #-}
{-# DISPLAY Initial.¡ _ = ¡ #-}
{-# DISPLAY Initial.¡-unique _ x = ¡-unique x #-}

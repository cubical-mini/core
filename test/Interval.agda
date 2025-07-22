module Interval where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete
open import Foundations.Quiver.Interval as Interval
open import Foundations.Quiver.Type

open import Notation.Push
open import Notation.Refl

open Interval.Category
module _ {ℓ-obᶠ : ℓ-sig 2 (0 , 0 , _) } {F : ob-sigᵈ _ ℓ-obᶠ}
  ⦃ _ : HPushω 𝐼 0 F ⦄ ⦃ _ : Lawful-Pushω 𝐼 λ b → Disc (F b _)  ⦄
  where

  -- one and two are identities

  one : F false _ → F false _
  one = push _

  _ : ∀{x} → x ＝ one x
  _ = push-refl

  two : F true _ → F true _
  two = push _

  _ : ∀{x} → x ＝ two x
  _ = push-refl

  -- the only non-trivial part is this function

  observe : F false _ → F true _
  observe = push _

  -- it means that lawful homegeneous push over the directed interval is just a function
  -- not that interesting

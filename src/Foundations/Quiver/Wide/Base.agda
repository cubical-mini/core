{-# OPTIONS --safe #-}
module Foundations.Quiver.Wide.Base where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Total.Base public

module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het} {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  (C : Quiver-onω m n Ob⁻ Ob⁺ ℓ-het) (open Quiver-onω C)
  {ℓ-homᵈ} (D : Quiver-onωᵈ Ob⁻ Ob⁺ Het 0 0 (λ _ _ → ⊤) (λ _ _ → ⊤) ℓ-homᵈ) where

  Wide : Quiver-onω m n Ob⁻ Ob⁺ (λ ℓx ℓy → ℓ-het ℓx ℓy ⊔ ℓ-homᵈ ℓx ℓy _ _)
  Wide .Quiver-onω.Het x y = ΣHet C D {x = x} {y = y} tt tt

{-# OPTIONS --safe #-}
module Foundations.Quiver.Wide.Base where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Total.Base public

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} {C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het} (open Quiver-onω C)
  {ℓ-homᵈ} (D : Quiver-onωᵈ C 0 (λ _ _ → ⊤ₜ) 0 (λ _ _ → ⊤ₜ) ℓ-homᵈ) where

  Wide : Quiver-onω m Ob⁻ n Ob⁺ (λ ℓx ℓy → ℓ-het ℓx ℓy ⊔ ℓ-homᵈ ℓx ℓy _ _)
  Wide .Quiver-onω.Het x y = ΣHet C D {x = x} {y = y} tt tt

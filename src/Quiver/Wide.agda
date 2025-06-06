{-# OPTIONS --safe #-}
module Quiver.Wide where

open import Prim.Data.Unit
open import Prim.Type

open import Quiver.Base
open import Quiver.Total

module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom ℓ-homᶠ : ℓ-sig²} {C : Quiverω ℓ-ob ℓ-hom} (open Quiverω C)
  (D : Quiverωᵈ C (λ _ → lzero) ℓ-homᶠ) (open Quiverωᵈ D) {t : ∀{ℓ} {x : Ob ℓ} → Ob[ x ]} where
  Wide : Quiverω ℓ-ob (λ ℓx ℓy → ℓ-hom ℓx ℓy ⊔ ℓ-homᶠ ℓx ℓy)
  Wide .Ob = Ob
  Wide .Hom x y = ΣHom C D {x = x} {y = y} t t
  Wide .refl .hom = refl
  Wide .refl .preserves = reflᵈ

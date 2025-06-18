{-# OPTIONS --safe #-}
module Notation.Wide where

open import Prim.Type

open import Notation.Base
open import Notation.Total

module _ {ℓ-ob ℓ-obᵈ : ℓ-sig¹} {ℓ-hom ℓ-homᶠ : ℓ-sig³} {C : Quiverω ℓ-ob ℓ-hom} (open Quiverω C)
  (D : Quiverωᵈ C ℓ-obᵈ ℓ-homᶠ) (open Quiverωᵈ D) (t : ∀{ℓ} {x : Ob ℓ} → Ob[ x ]) where
  Wide : Quiverω ℓ-ob (λ ℓ ℓx ℓy → ℓ-hom ℓ ℓx ℓy ⊔ ℓ-homᶠ ℓ ℓx ℓy)
  Wide .Ob = Ob
  Wide .Hom ℓ x y = ΣHom C D {x = x} {y = y} ℓ t t

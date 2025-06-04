{-# OPTIONS --safe #-}
module Foundations.IdentitySystem.Base where

open import Prim.Kan
open import Prim.Type

module _ {ℓ ℓr} {A : Type ℓ} (R : A → A → Type ℓr) (rfl : ∀ a → R a a) where
  record is-identity-system : Type (ℓ l⊔ ℓr) where
    no-eta-equality
    field
      to-path : {x y : A} → R x y → x ＝ y
      to-path-over
        : {x y : A} (p : R x y)
        → Pathᴾ (λ i → R x (to-path p i)) (rfl x) p

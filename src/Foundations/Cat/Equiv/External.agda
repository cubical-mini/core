{-# OPTIONS --safe #-}
module Foundations.Cat.Equiv.External where

open import Foundations.Prim.Type

open import Foundations.Cat.Composition
open import Foundations.Cat.Invertibility.External
open import Foundations.Cat.Structures.Quiver

open import Agda.Builtin.Sigma

module _ {C : Quiver} ⦃ _ : Comp C ⦄ (let open Quiver C) (ℓ : Level) {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (f : Hom x y) where

  is-equiv : Type (ob-lvl ℓ l⊔ hom-lvl ℓx ℓ l⊔ hom-lvl ℓy ℓ l⊔ hom-lvl ℓ ℓx l⊔ hom-lvl ℓ ℓy)
  is-equiv = Σ (is-inv-o ℓ f) λ _ → is-inv-i ℓ f

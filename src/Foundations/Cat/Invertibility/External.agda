{-# OPTIONS --safe #-}
module Foundations.Cat.Invertibility.External where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Foundations.Cat.Composition
open import Foundations.Cat.Structures.Quiver

open import Agda.Builtin.Sigma

module _ {C : Quiver} ⦃ _ : Comp C ⦄ (let open Quiver C) (ℓ : Level) {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (f : Hom x y) where

  is-inv-o : Type (ob-lvl ℓ l⊔ hom-lvl ℓ ℓx l⊔ hom-lvl ℓ ℓy)
  is-inv-o = (z : Ob ℓ) (h : Hom z y) → is-contr (Σ (Hom z x) λ g → g ∙ f ＝ h)

  is-inv-i : Type (ob-lvl ℓ l⊔ hom-lvl ℓx ℓ l⊔ hom-lvl ℓy ℓ)
  is-inv-i = (z : Ob ℓ) (h : Hom x z) → is-contr (Σ (Hom y z) λ g → f ∙ g ＝ h)

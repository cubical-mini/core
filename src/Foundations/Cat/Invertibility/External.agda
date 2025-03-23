{-# OPTIONS --safe #-}

module Control.Invertibility.External where

open import Prim.Kan
open import Prim.Type

open import Control.Structures.Quiver
open import Control.Composition
open import Control.Diagram.Coproduct.Indexed

private variable ℓx ℓy : Level

module _ {Q : Quiver} ⦃ _ : Comp Q ⦄ where
  open Quiver Q

  module _ {ℓ : Level} {x : Ob ℓx} {y : Ob ℓy} (f : Hom x y) where
    is-inv-o : Type (ob-lvl ℓ ⊔ hom-lvl ℓ ℓx ⊔ hom-lvl ℓ ℓy)
    is-inv-o = (z : Ob ℓ) (h : Hom z y)
             → is-contr (Σₜ (Hom z x) λ g → g ∙ f ≡ h)

    is-inv-i : Type (ob-lvl ℓ ⊔ hom-lvl ℓx ℓ ⊔ hom-lvl ℓy ℓ)
    is-inv-i = (z : Ob ℓ) (h : Hom x z)
             → is-contr (Σₜ (Hom y z) λ g → f ∙ g ≡ h)

{-# OPTIONS --safe #-}
module Notation.Representable where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity

module _ {ℓo ℓh : Level} {Ob : Type ℓo}
  (C : Small-quiver-on Ob ℓh) (open Small-quiver-on C) where

  Hom-action : (x y : Ob) → Type (ℓo l⊔ ℓh)
  Hom-action x y = (t : Ob) → Hom t x → Hom t y

  module _ ⦃ _ : Refl (Enlarge C) lzero ⦄ ⦃ _ : Comp (Enlarge C) lzero lzero lzero ⦄
    (C₂ : Small-2-quiver-on C) (open Small-2-quiver-on C₂) where
    Representable : {x y : Ob} (α : Hom-action x y) → Type (ℓo l⊔ ℓh)
    Representable {x} {y} α = {z : Ob} (g : Hom z x) → 2-Hom (g ∙ α x refl) (α z g)

    record Weak-parametric : Type (ℓo l⊔ ℓh) where
      no-eta-equality
      field param : {x y : Ob} (α : Hom-action x y) → Representable α

open Weak-parametric public

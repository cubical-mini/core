{-# OPTIONS --safe #-}
module Notation.Double.Composition where

open import Prim.Type

open import Notation.Composition
open import Notation.Double.Quiver
open import Notation.Quiver

module _ {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) {ℓ-hom□ : ℓ-square-sig}
  {Homₕ : hom-sig Ob (ℓ-homₕ ℓ-hom□)} ⦃ _ : Comp Ob Homₕ ⦄
  {Homᵥ : hom-sig Ob (ℓ-homᵥ ℓ-hom□)} ⦃ _ : Comp Ob Homᵥ ⦄
  (Hom□ : square-sig Ob Homₕ Homᵥ ℓ-hom□)
  where

  record ℂomp : Typeω where
    no-eta-equality
    infixl 90 _∙ₕ_ _∙ᵥ_
    field
      _∙ₕ_ : {ℓw ℓx ℓy ℓz ℓu ℓv : Level} {w : Ob ℓw} {x : Ob ℓx} {f : Homₕ w x}
             {y : Ob ℓy} {g : Homᵥ w y} {z : Ob ℓz} {h : Homᵥ x z} {k : Homₕ y z} (α : Hom□ f g h k)
             {u : Ob ℓu} {l : Homₕ x u} {v : Ob ℓv} {m : Homᵥ u v} {n : Homₕ z v} (β : Hom□ l h m n)
           → Hom□ (f ∙ l) g m (k ∙ n)
      _∙ᵥ_ : {ℓw ℓx ℓy ℓz ℓu ℓv : Level} {w : Ob ℓw} {x : Ob ℓx} {f : Homₕ w x}
             {y : Ob ℓy} {g : Homᵥ w y} {z : Ob ℓz} {h : Homᵥ x z} {k : Homₕ y z} (α : Hom□ f g h k)
             {u : Ob ℓu} {l : Homᵥ y u} {v : Ob ℓv} {m : Homᵥ z v} {n : Homₕ u v} (β : Hom□ k l m n)
           → Hom□ f (g ∙ l) (h ∙ m) n

open ℂomp ⦃ ... ⦄ public

{-# DISPLAY ℂomp._∙ₕ_ _ α β = α ∙ₕ β #-}
{-# DISPLAY ℂomp._∙ᵥ_ _ α β = α ∙ᵥ β #-}

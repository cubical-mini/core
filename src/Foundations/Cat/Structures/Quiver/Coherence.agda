{-# OPTIONS --safe #-}
module Control.Structures.Quiver.Coherence where

open import Prim.Type hiding (_∘_)
open import Prim.Interval renaming (trans to infixl 40 _∙_)

open import Control.Structures.Quiver.Base

module _ {o h} (Q : Quiver o h) where
  open Quiver Q
  has-composition : Type (o ⊔ h)
  has-composition = ∀ {x y z} → hom y z → hom x y → hom x z

  has-reflexivity : Type (o ⊔ h)
  has-reflexivity = ∀ x → hom x x

  module _ (_∘_ : has-composition) where
    has-associator : Type (o ⊔ h)
    has-associator = ∀ {x y z t} (f : hom x y) (g : hom y z) (h : hom z t)
                   → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f

    module _ (α : has-associator) where
      has-pentagonator : Type (o ⊔ h)
      has-pentagonator = ∀ {w x y z t}
                       → (f : hom w x) (g : hom x y) (h : hom y z) (k : hom z t)
                       → ap (k ∘_) (α f g h) ∙ (α f (h ∘ g) k) ∙ ap (_∘ f) (α g h k)
                       ≡ α (g ∘ f) h k ∙ α f g (k ∘ h)

    module _ (idn : has-reflexivity) where
      has-left-unitor : Type (o ⊔ h)
      has-left-unitor = ∀ {x y} (f : hom x y) → idn y ∘ f ≡ f

      has-right-unitor : Type (o ⊔ h)
      has-right-unitor = ∀ {x y} (f : hom x y) → f ∘ idn x ≡ f

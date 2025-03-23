```agda

module Data.Semicategory.Base where

open import Prim.Base

record Semicategory o h : Type₊ (o ⊔ h) where
  infixr 40 _∘_
  field
    Ob : Type o
    Hom : Ob → Ob → Type h
    _∘_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    assoc : ∀ {w x y z} (f : Hom w x) (g : Hom x y) (h : Hom y z)
          → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)



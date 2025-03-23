{-# OPTIONS --safe #-}

module Control.Category.Base where

open import Prim.Type
open import Prim.Interval
open import Prim.Path

record Semicategory o h : Type₊ (o ⊔ h) where
  field
    ob : Type o
    hom : ob → ob → Type h
    seq : ∀ {x y z} → hom x y → hom y z → hom x z 
    assoc : ∀ {x y z t} (f : hom x y) (g : hom y z) (h : hom z t)
            → seq (seq f g) h ≡ seq f (seq g h)

  -- notation
  -- α⟨_,_,_⟩ : ∀ {x y z t} (f : hom x y) (g : hom y z) (h : hom z t)
  --         → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
  -- α⟨_,_,_⟩ = assoc

  -- 𝟙⟨_⟩ : ∀ x → hom x x
  -- 𝟙⟨_⟩ = idn

  -- λ⟨_⟩ : ∀ {x y} (f : hom x y) → 𝟙⟨ x ⟩ ⋆ f ≡ f
  -- λ⟨_⟩ = idnl

  -- ρ⟨_⟩ : ∀ {x y} (f : hom x y) → f ⋆ 𝟙⟨ y ⟩ ≡ f
  -- ρ⟨_⟩ = idnr

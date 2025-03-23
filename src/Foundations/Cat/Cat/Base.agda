{-# OPTIONS --safe #-}

module Control.Cat.Base where

open import Prim.Type
open import Prim.Interval

  --is-identity : (_·_ : composition) → Type (o ⊔ h)
    
  --idn : ∀ x → hom x x
  -- idnl : ∀ {x y} (f : hom x y) → idn y · f ≡ f
  -- idnr : ∀ {x y} (f : hom x y) → f · idn x ≡ f

  -- pentagonator : (cmp : composition) → associator cmp → Type (o ⊔ h)
  -- pentagonator _⋆_ α = ∀ {x y z t w} →
  --   (f : hom x y) (g : hom y z) (h : hom z t) (k : hom t w)
  --   → {!!} ≡ α f (h ⋆ g) k ∙ {!!} ∙ {!!}

record precategory o h : Type₊ (o ⊔ h) where
  infixl 40 _⋆_
  field
    ob : Type o
    hom : ob → ob → Type h
    _⋆_ : ∀ {x y z} → hom x y → hom y z → hom x z 
    idn : ∀ x → hom x x
    idnl : ∀ {x y} (f : hom x y) → idn x ⋆ f ≡ f
    idnr : ∀ {x y} (f : hom x y) → f ⋆ idn y ≡ f
    assoc : ∀ {x y z t} (f : hom x y) (g : hom y z) (h : hom z t)
          → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)

  -- notation
  α⟨_,_,_⟩ : ∀ {x y z t} (f : hom x y) (g : hom y z) (h : hom z t)
          → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
  α⟨_,_,_⟩ = assoc

  𝟙⟨_⟩ : ∀ x → hom x x
  𝟙⟨_⟩ = idn

  λ⟨_⟩ : ∀ {x y} (f : hom x y) → 𝟙⟨ x ⟩ ⋆ f ≡ f
  λ⟨_⟩ = idnl

  ρ⟨_⟩ : ∀ {x y} (f : hom x y) → f ⋆ 𝟙⟨ y ⟩ ≡ f
  ρ⟨_⟩ = idnr

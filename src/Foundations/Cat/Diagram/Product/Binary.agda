{-# OPTIONS --safe #-}
module Control.Diagram.Product.Binary where

open import Prim.Kan
open import Prim.Type

open import Control.Composition
open import Control.Structures.Quiver

module _ (C : Quiver) ⦃ _ : Comp C ⦄ where
  open Quiver C

  record is-product ℓq {u v ℓp} {A : Ob u} {B : Ob v} {P : Ob ℓp} (π₁ : Hom P A) (π₂ : Hom P B) : Type (ob-lvl ℓq ⊔ hom-lvl ℓq u ⊔ hom-lvl ℓq v ⊔ hom-lvl ℓq ℓp) where
    no-eta-equality
    field
      ⟨_,_⟩ : {Q : Ob ℓq} (f : Hom Q A) (g : Hom Q B) → Hom Q P
      π₁∘⟨⟩ : {Q : Ob ℓq} {f : Hom Q A} {g : Hom Q B} → π₁ ∘ ⟨ f , g ⟩ ≡ f
      π₂∘⟨⟩ : {Q : Ob ℓq} {f : Hom Q A} {g : Hom Q B} → π₂ ∘ ⟨ f , g ⟩ ≡ g

      unique : {Q : Ob ℓq} {f : Hom Q A} {g : Hom Q B}
               {h : Hom Q P}
               (fs : π₁ ∘ h ≡ f) (sn : π₂ ∘ h ≡ g)
             → h ≡ ⟨ f , g ⟩

  record Product {u v} (A : Ob u) (B : Ob v) (P : Ob (u ⊔ v)) : Typeω where
    no-eta-equality
    field
      π₁  : Hom P A
      π₂  : Hom P B
      has-is-product : {ℓq : Level} → is-product ℓq π₁ π₂

  record Binary-products : Typeω where
    no-eta-equality
    infixr 80 _×_
    field
      _×_ : ∀ {u v} (A : Ob u) (B : Ob v) → Ob (u ⊔ v)
      has-product : ∀ {u v} {A : Ob u} {B : Ob v} → Product A B (A × B)


open is-product ⦃ ... ⦄ public
  renaming (unique to ⟨⟩-unique)
open Product ⦃ ... ⦄ public
  using (π₁; π₂)
open Binary-products ⦃ ... ⦄ public
  using (_×_)

{-# DISPLAY is-product.⟨_,_⟩ _ f g = ⟨ f , g ⟩ #-}
{-# DISPLAY is-product.π₁∘⟨⟩ _ = π₁∘⟨⟩ #-}
{-# DISPLAY is-product.π₂∘⟨⟩ _ = π₂∘⟨⟩ #-}
{-# DISPLAY is-product.unique _ p q = ⟨⟩-unique p q #-}
{-# DISPLAY Product.π₁ _ = π₁ #-}
{-# DISPLAY Product.π₂ _ = π₂ #-}
{-# DISPLAY Binary-products._×_ _ A B = A × B #-}

module _ {C : Quiver} ⦃ _ : Comp C ⦄ (let open Quiver C) where
  module _ ∀ {u v} {A : Ob u} {B : Ob v} where instance
    is-product-helper : {ℓq : Level} {P : Ob (u ⊔ v)} ⦃ p : Product C A B P ⦄ → is-product C ℓq π₁ π₂
    is-product-helper ⦃ p ⦄ = p .Product.has-is-product

    product-helper : ⦃ p : Binary-products C ⦄ → Product C A B (A × B)
    product-helper ⦃ p ⦄ = p .Binary-products.has-product

  infixr 81 _×→_
  _×→_ : ⦃ _ : Binary-products C ⦄
       → {u v ℓp ℓq : Level} {A : Ob u} {B : Ob v} {P : Ob ℓp} {Q : Ob ℓq}
       → Hom A P → Hom B Q → Hom (A × B) (P × Q)
  _×→_ f g = ⟨ π₁ ∙ f , π₂ ∙ g ⟩

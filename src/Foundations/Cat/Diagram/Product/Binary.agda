{-# OPTIONS --safe #-}
module Foundations.Cat.Diagram.Product.Binary where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Foundations.Cat.Composition
open import Foundations.Cat.Structures.Quiver

module _ (C : Quiver) ⦃ _ : Comp C ⦄ where
  open Quiver C

  record is-product ℓq {ℓa ℓb ℓp} {A : Ob ℓa} {B : Ob ℓb} {P : Ob ℓp} (π₁ : Hom P A) (π₂ : Hom P B) : Type (ob-lvl ℓq l⊔ hom-lvl ℓq ℓa l⊔ hom-lvl ℓq ℓb l⊔ hom-lvl ℓq ℓp) where
    no-eta-equality
    field
      ⟨_,_⟩ : {Q : Ob ℓq} (f : Hom Q A) (g : Hom Q B) → Hom Q P
      π₁∘⟨⟩ : {Q : Ob ℓq} {f : Hom Q A} {g : Hom Q B} → π₁ ∘ ⟨ f , g ⟩ ＝ f
      π₂∘⟨⟩ : {Q : Ob ℓq} {f : Hom Q A} {g : Hom Q B} → π₂ ∘ ⟨ f , g ⟩ ＝ g

      unique : {Q : Ob ℓq} {f : Hom Q A} {g : Hom Q B}
               {h : Hom Q P}
               (fs : π₁ ∘ h ＝ f) (sn : π₂ ∘ h ＝ g)
             → h ＝ ⟨ f , g ⟩

  record Product {ℓa ℓb} (A : Ob ℓa) (B : Ob ℓb) (P : Ob (ℓa l⊔ ℓb)) : Typeω where
    no-eta-equality
    field
      π₁  : Hom P A
      π₂  : Hom P B
      has-is-product : {ℓq : Level} → is-product ℓq π₁ π₂

  record Binary-products : Typeω where
    no-eta-equality
    infixr 80 _×_
    field
      _×_ : {ℓa ℓb : Level} (A : Ob ℓa) (B : Ob ℓb) → Ob (ℓa l⊔ ℓb)
      has-product : {ℓa ℓb : Level} {A : Ob ℓa} {B : Ob ℓb} → Product A B (A × B)


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
  module _ {ℓa ℓb : Level} {A : Ob ℓa} {B : Ob ℓb} where instance
    is-product-helper : {ℓq : Level} {P : Ob (ℓa l⊔ ℓb)} ⦃ p : Product C A B P ⦄ → is-product C ℓq π₁ π₂
    is-product-helper ⦃ p ⦄ = p .Product.has-is-product

    product-helper : ⦃ p : Binary-products C ⦄ → Product C A B (A × B)
    product-helper ⦃ p ⦄ = p .Binary-products.has-product

  infixr 81 _×→_
  _×→_ : ⦃ _ : Binary-products C ⦄
       → {ℓa ℓb ℓp ℓq : Level} {A : Ob ℓa} {B : Ob ℓb} {P : Ob ℓp} {Q : Ob ℓq}
       → Hom A P → Hom B Q → Hom (A × B) (P × Q)
  _×→_ f g = ⟨ π₁ ∙ f , π₂ ∙ g ⟩

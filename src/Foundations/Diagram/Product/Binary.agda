{-# OPTIONS --safe #-}
module Foundations.Diagram.Product.Binary where

open import Foundations.Base
open import Foundations.Cubical.HLevel.Base
open import Foundations.Discrete.Base
open import Foundations.Lens.Pull

open import Notation.Refl

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {ℓ-hom⁻}
  (A : HQuiver-onω m Ob⁻ ℓ-hom⁻) (open Quiver-onω A renaming (Het to Hom))
  {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} (H : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω H)
  ⦃ _ : Refl A ⦄ ⦃ hp : ∀{lys} {y : Ob⁺ lys} → Pull A 0 (λ x → Disc (Het x y)) ⦄ where

  record Product {lxs lys lps} (X : Ob⁺ lxs) (Y : Ob⁺ lys) (P : Ob⁻ lps) : Typeω where
    no-eta-equality
    field
      π₁ : Het P X
      π₂ : Het P Y
      ⟨_,_⟩ : ∀{ls} {Q : Ob⁻ ls} (f : Het Q X) (g : Het Q Y) → Hom Q P
      ⟨⟩◁π₁ : ∀{ls} {Q : Ob⁻ ls} {f : Het Q X} {g : Het Q Y} → ⟨ f , g ⟩ ◁ π₁ ＝ f
      ⟨⟩◁π₂ : ∀{ls} {Q : Ob⁻ ls} {f : Het Q X} {g : Het Q Y} → ⟨ f , g ⟩ ◁ π₂ ＝ g
      ⟨⟩-unique : ∀{ls} {Q : Ob⁻ ls} {f : Het Q X} {g : Het Q Y}
                → is-central {A = Σₜ (Hom Q P) (λ h → (h ◁ π₁ ＝ f) ×ₜ (h ◁ π₂ ＝ g))}
                    (⟨ f , g ⟩ , ⟨⟩◁π₁ , ⟨⟩◁π₂)

  record Binary-products (ℓ-× : Levels n → Levels n → Levels m) : Typeω where
    no-eta-equality
    infixr 80 _×_
    field
      _×_ : ∀{lxs lys} (X : Ob⁺ lxs) (Y : Ob⁺ lys) → Ob⁻ (ℓ-× lxs lys)
      has-product : ∀{lxs lys} {X : Ob⁺ lxs} {Y : Ob⁺ lys} → Product X Y (X × Y)

  open Product ⦃ ... ⦄ public
  open Binary-products ⦃ ... ⦄ public
    using (_×_)

{-# DISPLAY Product.π₁ _ = π₁ #-}
{-# DISPLAY Product.π₂ _ = π₂ #-}
{-# DISPLAY Product.⟨_,_⟩ _ f g = ⟨ f , g ⟩ #-}
{-# DISPLAY Product.⟨⟩◁π₁ _ = ⟨⟩◁π₁ #-}
{-# DISPLAY Product.⟨⟩◁π₂ _ = ⟨⟩◁π₂ #-}
{-# DISPLAY Product.⟨⟩-unique _ = ⟨⟩-unique #-}
{-# DISPLAY Binary-products._×_ _ X Y = X × Y #-}

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {ℓ-hom⁻}
  {A : HQuiver-onω m Ob⁻ ℓ-hom⁻} (open Quiver-onω A renaming (Het to Hom))
  {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} {H : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het} (open Quiver-onω H)
  ⦃ _ : Refl A ⦄ ⦃ hp : ∀{lys} {y : Ob⁺ lys} → Pull A 0 (λ x → Disc (Het x y)) ⦄ where instance

  Binary-products→Product : ∀{ℓ-× lxs lys} ⦃ bp : Binary-products A H ℓ-× ⦄
                            {X : Ob⁺ lxs} {Y : Ob⁺ lys}
                          → Product A H X Y (X × Y)
  Binary-products→Product ⦃ bp ⦄ = bp .Binary-products.has-product
  {-# OVERLAPPABLE Binary-products→Product #-}

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  ⦃ _ : Refl C ⦄ ⦃ hp : ∀{lys} {y : Ob lys} → Pull C 0 (λ x → Disc (Hom x y)) ⦄ where

  infixr 81 _×→_
  _×→_ : ∀{ℓ-× lxs lys lps lqs} ⦃ _ : Binary-products C C ℓ-× ⦄
         {X : Ob lxs} {Y : Ob lys} {P : Ob lps} {Q : Ob lqs}
       → Hom X P → Hom Y Q → Hom (X × Y) (P × Q)
  _×→_ f g = ⟨ π₁ ◁ f , π₂ ◁ g ⟩

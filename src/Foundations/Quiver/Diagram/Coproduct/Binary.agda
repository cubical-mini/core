{-# OPTIONS --safe #-}
module Foundations.Quiver.Diagram.Coproduct.Binary where

open import Foundations.HLevel.Base
open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete.Base
open import Foundations.Quiver.Lens.Push

open import Notation.Refl

module _ {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-hom⁺}
  (B : HQuiver-onω n Ob⁺ ℓ-hom⁺) (open Quiver-onω B renaming (Het to Hom))
  {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {ℓ-het}
  (H : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω H)
  ⦃ _ : Refl B ⦄ ⦃ hp : ∀{lxs} {x : Ob⁻ lxs} → Push B 0 (λ y → Disc (Het x y)) ⦄ where

  record Coproduct {lxs lys lss} (X : Ob⁻ lxs) (Y : Ob⁻ lys) (S : Ob⁺ lss) : Typeω where
    no-eta-equality
    field
      ι₁ : Het X S
      ι₂ : Het Y S
      ⁅_,_⁆ : ∀{ls} {Q : Ob⁺ ls} (f : Het X Q) (g : Het Y Q) → Hom S Q
      ι₁▷⁅⁆ : ∀{ls} {Q : Ob⁺ ls} {f : Het X Q} {g : Het Y Q} → ι₁ ▷ ⁅ f , g ⁆ ＝ f
      ι₂▷⁅⁆ : ∀{ls} {Q : Ob⁺ ls} {f : Het X Q} {g : Het Y Q} → ι₂ ▷ ⁅ f , g ⁆ ＝ g
      ⁅⁆-unique : ∀{ls} {Q : Ob⁺ ls} {f : Het X Q} {g : Het Y Q}
                → is-central⁺ (Σₜ (Hom S Q) (λ h → (ι₁ ▷ h ＝ f) ×ₜ (ι₂ ▷ h ＝ g)))
                    (⁅ f , g ⁆ , ι₁▷⁅⁆ , ι₂▷⁅⁆)

  record Binary-coproducts (ℓ-⊎ : Levels m → Levels m → Levels n) : Typeω where
    no-eta-equality
    infixr 70 _⊎_
    field
      _⊎_           : ∀{lxs lys} (X : Ob⁻ lxs) (Y : Ob⁻ lys) → Ob⁺ (ℓ-⊎ lxs lys)
      has-coproduct : ∀{lxs lys} {X : Ob⁻ lxs} {Y : Ob⁻ lys} → Coproduct X Y (X ⊎ Y)

  open Coproduct ⦃ ... ⦄ public
  open Binary-coproducts ⦃ ... ⦄ public
    using (_⊎_)

{-# DISPLAY Coproduct.ι₁ _ = ι₁ #-}
{-# DISPLAY Coproduct.ι₂ _ = ι₂ #-}
{-# DISPLAY Coproduct.⁅_,_⁆ _ f g = ⁅ f , g ⁆ #-}
{-# DISPLAY Coproduct.ι₁▷⁅⁆ _ = ι₁▷⁅⁆ #-}
{-# DISPLAY Coproduct.ι₂▷⁅⁆ _ = ι₂▷⁅⁆ #-}
{-# DISPLAY Coproduct.⁅⁆-unique _ = ⁅⁆-unique #-}
{-# DISPLAY Binary-coproducts._⊎_ _ X Y = X ⊎ Y #-}

module _ {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-hom⁺}
  {B : HQuiver-onω n Ob⁺ ℓ-hom⁺} (open Quiver-onω B renaming (Het to Hom))
  {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {ℓ-het}
  {H : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het} (open Quiver-onω H)
  ⦃ _ : Refl B ⦄ ⦃ hp : ∀{lxs} {x : Ob⁻ lxs} → Push B 0 (λ y → Disc (Het x y)) ⦄ where instance

  Binary-coproducts→Coproduct : ∀{ℓ-⊎ lxs lys} ⦃ bc : Binary-coproducts B H ℓ-⊎ ⦄
                                {X : Ob⁻ lxs} {Y : Ob⁻ lys}
                              → Coproduct B H X Y (X ⊎ Y)
  Binary-coproducts→Coproduct ⦃ bc ⦄ = bc .Binary-coproducts.has-coproduct
  {-# OVERLAPPABLE Binary-coproducts→Coproduct #-}

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  ⦃ _ : Refl C ⦄ ⦃ hp : ∀{lxs} {x : Ob lxs} → Push C 0 (λ y → Disc (Hom x y)) ⦄ where

  infixr 71 _⊎→_
  _⊎→_ : ∀{ℓ-⊎ lxs lys lss lqs} ⦃ _ : Binary-coproducts C C ℓ-⊎ ⦄
         {X : Ob lxs} {Y : Ob lys} {S : Ob lss} {Q : Ob lqs}
       → Hom S X → Hom Q Y → Hom (S ⊎ Q) (X ⊎ Y)
  _⊎→_ f g = ⁅ f ▷ ι₁ , g ▷ ι₂ ⁆

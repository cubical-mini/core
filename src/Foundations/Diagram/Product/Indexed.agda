module Foundations.Diagram.Product.Indexed where

open import Foundations.Base
open import Foundations.Cubical.HLevel.Base
open import Foundations.Discrete.Base
open import Foundations.Lens.Pull

open import Notation.Refl
open import Notation.Underlying

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {ℓ-hom⁻}
  (A : HQuiver-onω m Ob⁻ ℓ-hom⁻) (open Quiver-onω A renaming (Het to Hom))
  {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} (H : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω H)
  ⦃ _ : Refl A ⦄ ⦃ hp : ∀{lys} {y : Ob⁺ lys} → HPull A 0 (λ x → Disc (Het x y)) ⦄ where

  record Indexed-product {lix lfs lps} {Ix : Type lix} (F : Ix → Ob⁺ lfs) (P : Ob⁻ lps) : Typeω where
    no-eta-equality
    field
      π : ∀ i → Het P (F i)
      π-tuple   : ∀{lys} {Y : Ob⁻ lys} → (∀ i → Het Y (F i)) → Hom Y P
      π-commute : ∀{lys} {Y : Ob⁻ lys} {f : ∀ i → Het Y (F i)} {i} → π-tuple f ◁ π i ＝ f i
      π-unique  : ∀{lys} {Y : Ob⁻ lys} {f : ∀ i → Het Y (F i)}
                → is-central {A = Σₜ (Hom Y P) (λ h → (i : Ix) → h ◁ π i ＝ f i)} (π-tuple f , λ _ → π-commute)

  record Indexed-products {lix} (Ix : Type lix) (ℓ-Π : Levels n → Levels m) : Typeω where
    no-eta-equality
    field
      Π : ∀{lfs} (F : Ix → Ob⁺ lfs) → Ob⁻ (ℓ-Π lfs)
      has-indexed-product : ∀{lfs} {F : Ix → Ob⁺ lfs} → Indexed-product F (Π F)

  open Indexed-product ⦃ ... ⦄ public
  open Indexed-products ⦃ ... ⦄ public
    using (Π)

{-# DISPLAY Indexed-product.π _ i = π i #-}
{-# DISPLAY Indexed-product.π-tuple _ f = π-tuple f #-}
{-# DISPLAY Indexed-product.π-commute _ = π-commute #-}
{-# DISPLAY Indexed-product.π-unique _ = π-unique #-}

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {ℓ-hom⁻}
  {A : HQuiver-onω m Ob⁻ ℓ-hom⁻} (open Quiver-onω A renaming (Het to Hom))
  {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} {H : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het} (open Quiver-onω H)
  ⦃ _ : Refl A ⦄ ⦃ hp : ∀{lys} {y : Ob⁺ lys} → HPull A 0 (λ x → Disc (Het x y)) ⦄ where

  ∏[_] : ∀{lix ℓ-Π ls} {Ix : Type lix} ⦃ _ : Indexed-products A H Ix ℓ-Π ⦄
       → (Ix → Ob⁺ ls) → Ob⁻ (ℓ-Π ls)
  ∏[_] = Π

  infixr 60 Π-syntax
  Π-syntax : ∀{lix ls} ⦃ u : Underlying H ⦄ {ℓ-Π} (X : Ob⁺ lix) ⦃ _ : Indexed-products A H ⌞ X ⌟⁺ ℓ-Π ⦄
           → (⌞ X ⌟⁺ → Ob⁺ ls) → Ob⁻ (ℓ-Π ls)
  Π-syntax _ = Π
  syntax Π-syntax X (λ x → F) = Π[ x ꞉ X ] F

  instance
    Indexed-products→Indexed-product
      : ∀{lix ℓ-Π ls} {Ix : Type lix} ⦃ ip : Indexed-products A H Ix ℓ-Π ⦄
        {F : Ix → Ob⁺ ls}
      → Indexed-product A H F (Π F)
    Indexed-products→Indexed-product ⦃ ip ⦄ = ip .Indexed-products.has-indexed-product
    {-# OVERLAPPABLE Indexed-products→Indexed-product #-}

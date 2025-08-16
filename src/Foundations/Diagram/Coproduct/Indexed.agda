{-# OPTIONS --safe #-}
module Foundations.Diagram.Coproduct.Indexed where

open import Foundations.Base
open import Foundations.Cubical.HLevel.Base
open import Foundations.Lens.Push
open import Foundations.Path

open import Notation.Refl
open import Notation.Underlying

module _ {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-hom⁺}
  (B : HQuiver-onω n Ob⁺ ℓ-hom⁺) (open Quiver-onω B renaming (Het to Hom))
  {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {ℓ-het}
  (H : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω H)
  ⦃ _ : Refl B ⦄ ⦃ hp : ∀{lxs} {x : Ob⁻ lxs} → Push B 0 (λ y → Disc (Het x y)) ⦄ where

  record Indexed-coproduct {lix lfs lss} {Ix : Type lix} (F : Ix → Ob⁻ lfs) (S : Ob⁺ lss) : Typeω where
    no-eta-equality
    field
      ι : ∀ i → Het (F i) S
      ι-match   : ∀{lys} {Y : Ob⁺ lys} → (∀ i → Het (F i) Y) → Hom S Y
      ι-commute : ∀{lys} {Y : Ob⁺ lys} {f : ∀ i → Het (F i) Y} {i} → ι i ▷ ι-match f ＝ f i
      ι-unique : ∀{lys} {Y : Ob⁺ lys} {f : ∀ i → Het (F i) Y}
               → is-central {A = Σₜ (Hom S Y) (λ h → (i : Ix) → ι i ▷ h ＝ f i)} (ι-match f , λ _ → ι-commute)

  record Indexed-coproducts {lix} (Ix : Type lix) (ℓ-Σ : Levels m → Levels n) : Typeω where
    no-eta-equality
    field
      Σ : ∀{lfs} (F : Ix → Ob⁻ lfs) → Ob⁺ (ℓ-Σ lfs)
      has-indexed-coproduct : ∀{lfs} {F : Ix → Ob⁻ lfs} → Indexed-coproduct F (Σ F)

  open Indexed-coproduct ⦃ ... ⦄ public
  open Indexed-coproducts ⦃ ... ⦄ public
    using (Σ)

{-# DISPLAY Indexed-coproduct.ι _ i = ι i #-}
{-# DISPLAY Indexed-coproduct.ι-match _ f = ι-match f #-}
{-# DISPLAY Indexed-coproduct.ι-commute _ = ι-commute #-}
{-# DISPLAY Indexed-coproduct.ι-unique _ = ι-unique #-}

module _ {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-hom⁺}
  {B : HQuiver-onω n Ob⁺ ℓ-hom⁺} (open Quiver-onω B renaming (Het to Hom))
  {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {ℓ-het}
  {H : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het} (open Quiver-onω H)
  ⦃ _ : Refl B ⦄ ⦃ hp : ∀{lxs} {x : Ob⁻ lxs} → Push B 0 (λ y → Disc (Het x y)) ⦄ where

  Σ[_] : ∀{lix ℓ-Σ ls} {Ix : Type lix} ⦃ _ : Indexed-coproducts B H Ix ℓ-Σ ⦄
       → (Ix → Ob⁻ ls) → Ob⁺ (ℓ-Σ ls)
  Σ[_] = Σ

  infixr 60 Σ-syntax
  Σ-syntax : ∀{lix ls} ⦃ u : Underlying H ⦄ {ℓ-Σ} (X : Ob⁻ lix) ⦃ _ : Indexed-coproducts B H ⌞ X ⌟⁻ ℓ-Σ ⦄
           → (⌞ X ⌟⁻ → Ob⁻ ls) → Ob⁺ (ℓ-Σ ls)
  Σ-syntax _ = Σ
  syntax Σ-syntax X (λ x → F) = Σ[ x ꞉ X ] F

  instance
    Indexed-coproducts→Indexed-coproduct
      : ∀{lix ℓ-Σ ls} {Ix : Type lix} ⦃ ic : Indexed-coproducts B H Ix ℓ-Σ ⦄
        {F : Ix → Ob⁻ ls}
      → Indexed-coproduct B H F (Σ F)
    Indexed-coproducts→Indexed-coproduct ⦃ ic ⦄ = ic .Indexed-coproducts.has-indexed-coproduct
    {-# OVERLAPPABLE Indexed-coproducts→Indexed-coproduct #-}

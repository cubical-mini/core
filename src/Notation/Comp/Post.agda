{-# OPTIONS --safe #-}
module Notation.Comp.Post where

open import Foundations.Quiver.Base

module _
  {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het ℓ-hom⁺}
  {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺} (C : Quiver-onω m n Ob⁻ Ob⁺ ℓ-het) (open Quiver-onω C)
  (B : HQuiver-onω n Ob⁺ ℓ-hom⁺) (open Quiver-onω B renaming (Het to Hom))
  where

  record RComp lbs lxs lys : Type
    ( ℓ-ob⁻ lxs ⊔ ℓ-ob⁺ lbs ⊔ ℓ-ob⁺ lys ⊔ ℓ-het lxs lbs ⊔ ℓ-het lxs lys ⊔ ℓ-hom⁺ lys lbs) where
    no-eta-equality
    infixl 240 _▷_
    field _▷_ : {x : Ob⁻ lxs} {y : Ob⁺ lys} {b : Ob⁺ lbs}
              → Het x y → Hom y b
              → Het x b

  RCompω : Typeω
  RCompω = ∀{lbs lxs lys} → RComp lbs lxs lys

open RComp ⦃ ... ⦄ public
{-# DISPLAY RComp._▷_ _ α g = α ▷ g #-}


module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het ℓ-hom⁺}
  {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺} (C : Quiver-onω m n Ob⁻ Ob⁺ ℓ-het) (open Quiver-onω C)
  (B : HQuiver-onω n Ob⁺ ℓ-hom⁺) (open Quiver-onω B renaming (Het to Hom))
  {m′ n′ ℓ-obᵈ⁻ ℓ-obᵈ⁺ ℓ-hetᵈ ℓ-homᵈ⁺}
  {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺}
  (D : Quiver-onωᵈ Ob⁻ Ob⁺ Het m′ n′ Ob[_]⁻ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D)
  (B′ : HQuiver-onωᵈ Ob⁺ Hom n′ Ob[_]⁺ ℓ-homᵈ⁺) (open Quiver-onωᵈ B′ renaming (Het[_] to Hom[_]))
  ⦃ _ : RCompω C B ⦄ where

  record RCompᵈ lbs lxs lys lbsᵈ lxsᵈ lysᵈ : Type
    ( ℓ-ob⁻ lxs ⊔ ℓ-ob⁺ lbs ⊔ ℓ-ob⁺ lys ⊔ ℓ-het lxs lys ⊔ ℓ-hom⁺ lys lbs ⊔ ℓ-obᵈ⁻ lxs lxsᵈ
    ⊔ ℓ-obᵈ⁺ lbs lbsᵈ ⊔ ℓ-obᵈ⁺ lys lysᵈ ⊔ ℓ-hetᵈ lxs lbs lxsᵈ lbsᵈ
    ⊔ ℓ-hetᵈ lxs lys lxsᵈ lysᵈ ⊔ ℓ-homᵈ⁺ lys lbs lysᵈ lbsᵈ) where
    no-eta-equality
    infixl 250 _▷ᵈ_
    field
      _▷ᵈ_ : {x : Ob⁻ lxs} {y : Ob⁺ lys} {b : Ob⁺ lbs}
             {α : Het x y} {g : Hom y b}
             {x′ : Ob[ x ]⁻ lxsᵈ} {y′ : Ob[ y ]⁺ lysᵈ} {b′ : Ob[ b ]⁺ lbsᵈ}
           → Het[ α ] x′ y′ → Hom[ g ] y′ b′
           → Het[ α ▷ g  ] x′ b′

  RCompωᵈ : Typeω
  RCompωᵈ = ∀{lbs lxs lys lbsᵈ lxsᵈ lysᵈ} → RCompᵈ lbs lxs lys lbsᵈ lxsᵈ lysᵈ

open RCompᵈ ⦃ ... ⦄ public
{-# DISPLAY RCompᵈ._▷ᵈ_ _ α g = α ▷ᵈ g #-}

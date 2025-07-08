{-# OPTIONS --safe #-}
module Foundations.Quiver.Total.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Total.Base

open import Notation.Comp.Double
open import Notation.Comp.Homo
open import Notation.Comp.Post
open import Notation.Comp.Pre
open import Notation.Refl
open import Notation.Sym

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {m′ ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  {D : HQuiver-onωᵈ Ob Hom m′ Ob[_] ℓ-homᵈ} where instance

  ∫-Refl : ⦃ _ : Reflω C ⦄ ⦃ _ : Reflωᵈ C D ⦄ → Reflω (∫ C D)
  ∫-Refl .refl .fst = refl
  ∫-Refl .refl .snd = reflᵈ _

  ∫-Sym : ⦃ _ : Symω C ⦄ ⦃ _ : Symωᵈ C D ⦄ → Symω (∫ C D)
  ∫-Sym .sym p .fst = sym  (p .fst)
  ∫-Sym .sym p .snd = symᵈ (p .snd)

  ∫-HComp : ⦃ _ : HCompω C ⦄ ⦃ _ : HCompωᵈ C D ⦄ → HCompω (∫ C D)
  ∫-HComp ._∙_ p q .fst = p .fst ∙ q .fst
  ∫-HComp ._∙_ p q .snd = p .snd ∙ᵈ q .snd

{-# INCOHERENT ∫-Refl ∫-Sym ∫-HComp #-}

module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het} {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  {C : Quiver-onω m n Ob⁻ Ob⁺ ℓ-het} (open Quiver-onω C)
  {m′ n′ ℓ-obᵈ⁻ ℓ-obᵈ⁺ ℓ-hetᵈ} {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺}
  {D : Quiver-onωᵈ Ob⁻ Ob⁺ Het m′ n′ Ob[_]⁻ Ob[_]⁺ ℓ-hetᵈ} where

  module _ {ℓ-hom⁻ ℓ-homᵈ⁻} {A : HQuiver-onω m Ob⁻ ℓ-hom⁻}
    {A′ : HQuiver-onωᵈ Ob⁻ _ m′ _ ℓ-homᵈ⁻} where instance

    ∫-LComp : ⦃ _ : LCompω C A ⦄ ⦃ _ : LCompωᵈ C A D A′ ⦄ → LCompω (∫ C D) (∫ A A′)
    ∫-LComp ._◁_ α p .fst = α .fst ◁ p .fst
    ∫-LComp ._◁_ α p .snd = α .snd ◁ᵈ p .snd

  module _ {ℓ-hom⁺ ℓ-homᵈ⁺} {B : HQuiver-onω n Ob⁺ ℓ-hom⁺}
    {B′ : HQuiver-onωᵈ Ob⁺ _ n′ _ ℓ-homᵈ⁺} where instance

    ∫-RComp : ⦃ _ : RCompω C B ⦄ ⦃ _ : RCompωᵈ C B D B′ ⦄ → RCompω (∫ C D) (∫ B B′)
    ∫-RComp ._▷_ α p .fst = α .fst ▷ p .fst
    ∫-RComp ._▷_ α p .snd = α .snd ▷ᵈ p .snd

  module _ {ℓ-hom⁻ ℓ-hom⁺ ℓ-homᵈ⁻ ℓ-homᵈ⁺} {A : HQuiver-onω m Ob⁻ ℓ-hom⁻} {B : HQuiver-onω n Ob⁺ ℓ-hom⁺}
    {A′ : HQuiver-onωᵈ Ob⁻ _ m′ _ ℓ-homᵈ⁻} {B′ : HQuiver-onωᵈ Ob⁺ _ n′ _ ℓ-homᵈ⁺}
    where instance

    ∫-DComp : ⦃ _ : DCompω C A B ⦄ ⦃ _ : DCompωᵈ C A B D A′ B′ ⦄ → DCompω (∫ C D) (∫ A A′) (∫ B B′)
    ∫-DComp ._∙∙_∙∙_ p α q .fst = p .fst ∙∙ α .fst ∙∙ q .fst
    ∫-DComp ._∙∙_∙∙_ p α q .snd = p .snd ∙∙ α .snd ∙∙ᵈ q .snd

{-# INCOHERENT ∫-LComp ∫-RComp ∫-DComp #-} -- TODO check

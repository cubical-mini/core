{-# OPTIONS --safe #-}
module Foundations.Quiver.Wide.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Total.Groupoid
open import Foundations.Quiver.Wide.Base


open import Notation.Comp.Double
open import Notation.Comp.Homo
open import Notation.Comp.Post
open import Notation.Comp.Pre
open import Notation.Refl
open import Notation.Sym

module _ {m ℓ-ob ℓ-het} {Ob : ob-sig ℓ-ob} {C : HQuiver-onω m Ob ℓ-het}
  {ℓ-homᵈ} {D : Quiver-onωᵈ Ob Ob _ 0 0 (λ _ _ → ⊤) (λ _ _ → ⊤) ℓ-homᵈ} where instance

  Wide-Refl : ⦃ _ : Reflω C ⦄ ⦃ _ : Reflωᵈ C D ⦄ → Reflω (Wide C D)
  Wide-Refl .refl .fst = refl
  Wide-Refl .refl .snd = reflᵈ _

  Wide-Sym : ⦃ _ : Symω C ⦄ ⦃ _ : Symωᵈ C D ⦄ → Symω (Wide C D)
  Wide-Sym .sym p .fst = sym  (p .fst)
  Wide-Sym .sym p .snd = symᵈ (p .snd)

  Wide-HComp : ⦃ _ : HCompω C ⦄ ⦃ _ : HCompωᵈ C D ⦄ → HCompω (Wide C D)
  Wide-HComp ._∙_ p q .fst = p .fst ∙ q .fst
  Wide-HComp ._∙_ p q .snd = p .snd ∙ᵈ q .snd

{-# INCOHERENT Wide-Refl Wide-Sym Wide-HComp #-}

module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het} {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  {C : Quiver-onω m n Ob⁻ Ob⁺ ℓ-het}
  {ℓ-homᵈ} {D : Quiver-onωᵈ Ob⁻ Ob⁺ _ 0 0 (λ _ _ → ⊤) (λ _ _ → ⊤) ℓ-homᵈ} where

  module _ {ℓ-hom⁻ ℓ-homᵈ⁻} {A : HQuiver-onω m Ob⁻ ℓ-hom⁻}
    {A′ : HQuiver-onωᵈ Ob⁻ _ 0 _ ℓ-homᵈ⁻} where instance

    Wide-LComp : ⦃ _ : LCompω C A ⦄ ⦃ _ : LCompωᵈ C A D A′ ⦄ → LCompω (Wide C D) (Wide A A′)
    Wide-LComp ._◁_ α p .fst = α .fst ◁ p .fst
    Wide-LComp ._◁_ α p .snd = α .snd ◁ᵈ p .snd

  module _ {ℓ-hom⁺ ℓ-homᵈ⁺} {B : HQuiver-onω n Ob⁺ ℓ-hom⁺}
    {B′ : HQuiver-onωᵈ Ob⁺ _ 0 _ ℓ-homᵈ⁺} where instance

    Wide-RComp : ⦃ _ : RCompω C B ⦄ ⦃ _ : RCompωᵈ C B D B′ ⦄ → RCompω (Wide C D) (Wide B B′)
    Wide-RComp ._▷_ α p .fst = α .fst ▷ p .fst
    Wide-RComp ._▷_ α p .snd = α .snd ▷ᵈ p .snd

  module _ {ℓ-hom⁻ ℓ-hom⁺ ℓ-homᵈ⁻ ℓ-homᵈ⁺} {A : HQuiver-onω m Ob⁻ ℓ-hom⁻} {B : HQuiver-onω n Ob⁺ ℓ-hom⁺}
    {A′ : HQuiver-onωᵈ Ob⁻ _ 0 _ ℓ-homᵈ⁻} {B′ : HQuiver-onωᵈ Ob⁺ _ 0 _ ℓ-homᵈ⁺}
    where instance

    Wide-DComp : ⦃ _ : DCompω C A B ⦄ ⦃ _ : DCompωᵈ C A B D A′ B′ ⦄ → DCompω (Wide C D) (Wide A A′) (Wide B B′)
    Wide-DComp ._∙∙_∙∙_ p α q .fst = p .fst ∙∙ α .fst ∙∙ q .fst
    Wide-DComp ._∙∙_∙∙_ p α q .snd = p .snd ∙∙ α .snd ∙∙ᵈ q .snd

{-# INCOHERENT Wide-LComp Wide-RComp Wide-DComp #-} -- TODO check

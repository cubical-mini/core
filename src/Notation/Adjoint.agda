{-# OPTIONS --safe #-}
module Notation.Adjoint where

open import Prim.Kan
open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Unitality.Inner
open import Notation.Unitality.Outer
open import Notation.Whiskering.Left
open import Notation.Whiskering.Right

-- NB: can use ω classes if this is too slow
module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  {ℓc ℓd : Level} {c : Ob ℓc} {d : Ob ℓd}
  ⦃ _ : Refl C ℓc ⦄ ⦃ _ : Refl C ℓd ⦄
  ⦃ _ : Comp C ℓd ℓd ℓc ⦄ ⦃ _ : Comp C ℓc ℓc ℓd ⦄ ⦃ _ : Comp C ℓc ℓd ℓd ⦄ ⦃ _ : Comp C ℓd ℓc ℓc ⦄ ⦃ _ : Comp C ℓd ℓc ℓd ⦄ ⦃ _ : Comp C ℓc ℓd ℓc ⦄
  ⦃ _ : Whisker-l C C₂ ℓc ℓd ℓd ⦄ ⦃ _ : Whisker-l C C₂ ℓd ℓc ℓc ⦄
  ⦃ _ : Whisker-r C C₂ ℓc ℓc ℓd ⦄ ⦃ _ : Whisker-r C C₂ ℓd ℓd ℓc ⦄
  ⦃ _ : Refl (Quiver₂ c d) ℓc ⦄ ⦃ _ : Refl (Quiver₂ d c) ℓd ⦄
  ⦃ _ : Comp (Quiver₂ c d) ℓc ℓc ℓc ⦄ ⦃ _ : Comp (Quiver₂ d c) ℓd ℓd ℓd ⦄
  ⦃ _ : Assoc C (C₂ ²ᵒᵖω) ℓc ℓd ℓc ℓd ⦄ ⦃ _ : Unit-i C (C₂ ²ᵒᵖω) ℓc ℓd ⦄ ⦃ _ : Unit-o C C₂ ℓc ℓd ⦄
  ⦃ _ : Assoc C C₂ ℓd ℓc ℓd ℓc ⦄ ⦃ _ : Unit-o C (C₂ ²ᵒᵖω) ℓd ℓc ⦄ ⦃ _ : Unit-i C C₂ ℓd ℓc ⦄ where

  record Adjoint (L : Hom c d) (R : Hom d c) : Type (ℓ-hom ℓc ℓc l⊔ ℓ-hom ℓd ℓd l⊔ ℓ-hom ℓc ℓd l⊔ ℓ-hom ℓd ℓc) where
    no-eta-equality
    field
      η   : 2-Hom refl (L ∙ R)
      ε   : 2-Hom (R ∙ L) refl
      zig : id-i L ∙ (η ▷ L) ∙ assoc L R L ∙ (L ◁ ε) ∙ id-o L ＝ refl
      zag : id-o R ∙ (R ◁ η) ∙ assoc R L R ∙ (ε ▷ R) ∙ id-i R ＝ refl


module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C) {C₂ : 2-Quiver-on C} (open 2-Quiver-on C₂)
  {ℓc ℓd : Level} {c : Ob ℓc} {d : Ob ℓd}
  ⦃ _ : Refl C ℓc ⦄ ⦃ _ : Refl C ℓd ⦄
  ⦃ _ : Comp C ℓd ℓd ℓc ⦄ ⦃ _ : Comp C ℓc ℓc ℓd ⦄ ⦃ _ : Comp C ℓc ℓd ℓd ⦄ ⦃ _ : Comp C ℓd ℓc ℓc ⦄ ⦃ _ : Comp C ℓd ℓc ℓd ⦄ ⦃ _ : Comp C ℓc ℓd ℓc ⦄
  ⦃ _ : Whisker-l C C₂ ℓc ℓd ℓd ⦄ ⦃ _ : Whisker-l C C₂ ℓd ℓc ℓc ⦄
  ⦃ _ : Whisker-r C C₂ ℓc ℓc ℓd ⦄ ⦃ _ : Whisker-r C C₂ ℓd ℓd ℓc ⦄
  ⦃ _ : Refl (Quiver₂ c d) ℓc ⦄ ⦃ _ : Refl (Quiver₂ d c) ℓd ⦄
  ⦃ _ : Comp (Quiver₂ c d) ℓc ℓc ℓc ⦄ ⦃ _ : Comp (Quiver₂ d c) ℓd ℓd ℓd ⦄
  ⦃ _ : Assoc C (C₂ ²ᵒᵖω) ℓc ℓd ℓc ℓd ⦄ ⦃ _ : Unit-i C (C₂ ²ᵒᵖω) ℓc ℓd ⦄ ⦃ _ : Unit-o C C₂ ℓc ℓd ⦄
  ⦃ _ : Assoc C C₂ ℓd ℓc ℓd ℓc ⦄ ⦃ _ : Unit-o C (C₂ ²ᵒᵖω) ℓd ℓc ⦄ ⦃ _ : Unit-i C C₂ ℓd ℓc ⦄ where

  infix 10 _⊣_
  _⊣_ : Hom c d → Hom d c → Type (ℓ-hom ℓc ℓc l⊔ ℓ-hom ℓc ℓd l⊔ ℓ-hom ℓd ℓc l⊔ ℓ-hom ℓd ℓd)
  _⊣_ = Adjoint C C₂

{-# DISPLAY Adjoint C C₂ L R = _⊣_ {C = C} {C₂ = C₂} L R #-}

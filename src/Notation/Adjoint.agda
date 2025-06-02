{-# OPTIONS --safe #-}
module Notation.Adjoint where

open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Symmetry
open import Notation.Unitality.Inner
open import Notation.Unitality.Outer
open import Notation.Whiskering.Left
open import Notation.Whiskering.Right

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂) (C₃ : 3-Quiver-on C C₂) (open 3-Quiver-on C₃)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ ⦃ _ : Assocω C C₂ ⦄ ⦃ _ : Unit-iω C C₂ ⦄ ⦃ _ : Unit-oω C C₂ ⦄
  ⦃ _ : Whisker-lω C C₂ ⦄ ⦃ _ : Whisker-rω C C₂ ⦄
  ⦃ _ : Reflω₂ C C₂ ⦄ ⦃ _ : Symmetryω₂ C C₂ ⦄ ⦃ _ : Compω₂ C C₂ ⦄
  where

  record Adjoint {ℓc ℓd} {c : Ob ℓc} {d : Ob ℓd} (L : Hom c d) (R : Hom d c) : Type (ℓ-hom ℓc ℓc l⊔ ℓ-hom ℓd ℓd l⊔ ℓ-hom ℓc ℓd l⊔ ℓ-hom ℓd ℓc) where
    no-eta-equality
    field
      η   : 2-Hom refl (L ∙ R)
      ε   : 2-Hom (R ∙ L) refl
      zig : 3-Hom (sym (id-i L) ∙ (η ▷ L) ∙ sym (assoc L R L) ∙ (L ◁ ε) ∙ id-o L) refl
      zag : 3-Hom (sym (id-o R) ∙ (R ◁ η) ∙      assoc R L R  ∙ (ε ▷ R) ∙ id-i R) refl

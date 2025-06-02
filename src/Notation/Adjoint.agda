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

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄
  ⦃ _ : Assocω C C₂ ⦄        ⦃ _ : Unit-iω C C₂ ⦄        ⦃ _ : Unit-oω C C₂ ⦄
  ⦃ _ : Assocω C (C₂ ²ᵒᵖω) ⦄ ⦃ _ : Unit-iω C (C₂ ²ᵒᵖω) ⦄ ⦃ _ : Unit-oω C (C₂ ²ᵒᵖω) ⦄
  ⦃ _ : Whisker-lω C C₂ ⦄ ⦃ _ : Whisker-rω C C₂ ⦄
  ⦃ _ : ∀{ℓc ℓd} {c : Ob ℓc} {d : Ob ℓd} → Reflω (Quiver₂ c d) ⦄
  ⦃ _ : ∀{ℓc ℓd} {c : Ob ℓc} {d : Ob ℓd} → Compω (Quiver₂ c d) ⦄
  where

  record Adjoint {ℓc ℓd} {c : Ob ℓc} {d : Ob ℓd} (L : Hom c d) (R : Hom d c) : Type (ℓ-hom ℓc ℓc l⊔ ℓ-hom ℓd ℓd l⊔ ℓ-hom ℓc ℓd l⊔ ℓ-hom ℓd ℓc) where
    no-eta-equality
    field
      η   : 2-Hom refl (L ∙ R)
      ε   : 2-Hom (R ∙ L) refl
      zig : id-i L ∙ (η ▷ L) ∙ assoc L R L ∙ (L ◁ ε) ∙ id-o L ＝ refl
      zag : id-o R ∙ (R ◁ η) ∙ assoc R L R ∙ (ε ▷ R) ∙ id-i R ＝ refl


module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C) {C₂ : 2-Quiver-on C} (open 2-Quiver-on C₂)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄
  ⦃ _ : Assocω C C₂ ⦄ ⦃ _ : Unit-iω C C₂ ⦄ ⦃ _ : Unit-oω C C₂ ⦄
  ⦃ _ : Assocω C (C₂ ²ᵒᵖω) ⦄ ⦃ _ : Unit-iω C (C₂ ²ᵒᵖω) ⦄ ⦃ _ : Unit-oω C (C₂ ²ᵒᵖω) ⦄
  ⦃ _ : Whisker-lω C C₂ ⦄ ⦃ _ : Whisker-rω C C₂ ⦄
  ⦃ _ : ∀{ℓc ℓd} {c : Ob ℓc} {d : Ob ℓd} → Reflω (Quiver₂ c d) ⦄
  ⦃ _ : ∀{ℓc ℓd} {c : Ob ℓc} {d : Ob ℓd} → Compω (Quiver₂ c d) ⦄
  where
  infix 10 _⊣_
  _⊣_ : ∀{ℓc ℓd}{c : Ob ℓc} {d : Ob ℓd} → Hom c d → Hom d c → Type (ℓ-hom ℓc ℓc l⊔ ℓ-hom ℓc ℓd l⊔ ℓ-hom ℓd ℓc l⊔ ℓ-hom ℓd ℓd)
  _⊣_ = Adjoint C C₂

{-# DISPLAY Adjoint C C₂ {_} {_} {c} {d} L R = _⊣_ {C = C} {C₂ = C₂} {c} {d} L R #-}

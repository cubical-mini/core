{-# OPTIONS --safe #-}
module Notation.Double.Adjunction where

-- TODO conjoints

-- open import Prim.Type

-- open import Notation.Associativity
-- open import Notation.Composition
-- open import Notation.Double.Composition
-- open import Notation.Double.Quiver
-- open import Notation.Double.Reflexivity
-- open import Notation.Quiver
-- open import Notation.Reflexivity
-- open import Notation.Unitality.Inner
-- open import Notation.Unitality.Outer

-- module _ {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) {ℓ-hom□ : ℓ-sq-sig}
--   {Homₕ : hom-sig Ob (ℓ-hor ℓ-hom□)} ⦃ _ : Refl Ob Homₕ ⦄ ⦃ _ : Comp Ob Homₕ ⦄
--   {Homᵥ : hom-sig Ob (ℓ-ver ℓ-hom□)} ⦃ _ : Refl Ob Homᵥ ⦄ ⦃ _ : Comp Ob Homᵥ ⦄
--   (Hom□ : sq-sig Ob Homₕ Homᵥ ℓ-hom□) ⦃ _ : ℝefl Ob Hom□ ⦄ ⦃ _ : ℂomp Ob Hom□ ⦄
--   ⦃ _ : Assoc Ob Homₕ λ f g → Hom□ g refl refl f ⦄ ⦃ _ : Unit-i Ob Homₕ λ f g → Hom□ f (refl ∙ refl) (refl ∙ refl) g ⦄ ⦃ _ : Unit-o Ob Homₕ λ f g → Hom□ g refl refl f ⦄
--   ⦃ _ : Assoc Ob Homₕ λ f g → Hom□ f refl refl g ⦄ ⦃ _ : Unit-i Ob Homₕ λ f g → Hom□ g refl refl f ⦄ ⦃ _ : Unit-o Ob Homₕ λ f g → Hom□ f (refl ∙ refl) (refl ∙ refl) g ⦄
--   (_~_ : {ℓw ℓx ℓy ℓz : Level} {w : Ob ℓw} {x : Ob ℓx} {f : Homₕ w x} {y : Ob ℓy} {g : Homᵥ w y} {z : Ob ℓz} {h : Homᵥ x z} {k : Homₕ y z} (α β : Hom□ f g h k) → Type (ℓ-hom□ ℓw ℓx ℓy ℓz)) where

--   record Weak-Adjunction {ℓc ℓd : Level} {C : Ob ℓc} {D : Ob ℓd} (L : Homₕ C D) (R : Homₕ D C) : Typeω where
--     no-eta-equality
--     field
--       η   : Hom□ refl refl refl (L ∙ R)
--       ε   : Hom□ (R ∙ L) refl refl refl
--       zig : ((η ∙ₕ reflᵥ) ∙ᵥ assoc L R L ∙ᵥ (reflᵥ ∙ₕ ε)) ~ (∙-id-i L ∙ᵥ ∙-id-o L)
--       zag : ((reflᵥ ∙ₕ η) ∙ᵥ assoc R L R ∙ᵥ (ε ∙ₕ reflᵥ)) ~ (∙-id-o R ∙ᵥ ∙-id-i R)

-- module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom□ : ℓ-square-sig}
--   {Homₕ : hom-sig Ob (ℓ-homₕ ℓ-hom□)} ⦃ _ : Refl Ob Homₕ ⦄ ⦃ _ : Comp Ob Homₕ ⦄
--   {Homᵥ : hom-sig Ob (ℓ-homᵥ ℓ-hom□)} ⦃ _ : Refl Ob Homᵥ ⦄ ⦃ _ : Comp Ob Homᵥ ⦄
--   {Hom□ : square-sig Ob Homₕ Homᵥ ℓ-hom□} ⦃ _ : ℝefl Ob Hom□ ⦄ ⦃ _ : ℂomp Ob Hom□ ⦄
--   ⦃ _ : Assoc Ob Homₕ λ f g → Hom□ g refl refl f ⦄ ⦃ _ : Unit-i Ob Homₕ λ f g → Hom□ f (refl ∙ refl) (refl ∙ refl) g ⦄ ⦃ _ : Unit-o Ob Homₕ λ f g → Hom□ g refl refl f ⦄
--   ⦃ _ : Assoc Ob Homₕ λ f g → Hom□ f refl refl g ⦄ ⦃ _ : Unit-i Ob Homₕ λ f g → Hom□ g refl refl f ⦄ ⦃ _ : Unit-o Ob Homₕ λ f g → Hom□ f (refl ∙ refl) (refl ∙ refl) g ⦄ where

--   infix 1 _⊣_
--   _⊣_ : {ℓc ℓd : Level} {C : Ob ℓc} {D : Ob ℓd} (L : Homₕ C D) (R : Homₕ D C) → Typeω
--   L ⊣ R = Weak-Adjunction Ob Hom□ _＝_ L R
--   {-# NOINLINE _⊣_ #-}

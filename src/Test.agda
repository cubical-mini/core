{-# OPTIONS --safe --default-level #-}
module Test where

open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Notation.Associativity
open import Notation.Composition
open import Notation.Double.Composition
open import Notation.Double.Interchange
open import Notation.Double.Quiver
open import Notation.Quiver
open import Notation.Reflexivity
open import Notation.Double.Reflexivity
open import Notation.Unitality.Inner
open import Notation.Unitality.Outer

module _ {ℓa : Level} {A : Type ℓa} where
  Pa : Quiver-on (λ _ → A)
  Pa .Quiver-on.ℓ-hom = _
  Pa .Quiver-on.Hom = _＝_

  Sq : ℚuiver-on (λ _ → A)
  Sq .ℚuiver-on.ℓ-hom□ = _
  Sq .ℚuiver-on.Homₕ = _＝_
  Sq .ℚuiver-on.Homᵥ = _＝_
  Sq .ℚuiver-on.Hom□ p q r s = Pathᴾ (λ i → q i ＝ r i) p s

  instance
    pare : Refl (λ _ → A) _＝_
    pare .Refl.refl {x} _ = x

    sqre : ℝefl (λ _ → A) (λ p q r s → Pathᴾ (λ i → Path A (q i) (r i)) p s)
    sqre .ℝefl.reflₕ {f} i _ = f i
    sqre .ℝefl.reflᵥ {f} _ j = f j


module _ {ℓa : Level} {A : Type ℓa} {x y : A} {p : x ＝ y} where
  zook : Pathᴾ (λ i → p i ＝ p i) refl refl
  zook = reflₕ

  kooz : p ＝ p
  kooz = reflᵥ

Fun : ∀{ℓa ℓb} → Type ℓa → Type ℓb → Type (ℓa l⊔ ℓb)
Fun A B = A → B

Funs : Quiver-on (λ ℓ → Type ℓ)
Funs .Quiver-on.ℓ-hom = _
Funs .Quiver-on.Hom = Fun

instance
  Funs-Comp : Comp _ Fun
  Funs-Comp .Comp._∙_ f g x = g (f x)

  Funs-Assoc : Assoc _ Fun _＝_
  Funs-Assoc .Assoc.assoc f g h i x = h (g (f x))

open import Prim.Data.Sigma
Rels : (ℓ : Level) → Quiver-on (λ _ → Type ℓ)
Rels ℓ .Quiver-on.ℓ-hom = _
Rels ℓ .Quiver-on.Hom X Y = Σₜ (Type ℓ) λ S → (S → X) ×ₜ (S → Y)

-- open import Prim.Equiv
-- instance
--   Rels-Comp : ∀{ℓ} → Comp _ (Rels ℓ)
--   Rels-Comp {ℓ} .Comp._∙_ (R , f , g) (S , h , k) = (Σ R (λ _ → S)) , (λ x₁ → f (x₁ .fst)) , λ z₁ → k (z₁ .snd)

--   Rels-Assoc : ∀{ℓ} → Assoc (Rels ℓ) λ A B → Lift _ {!!}
--   Rels-Assoc .Assoc.assoc f g h .lower = {!!}

module _ where private
  open Quiver-on Funs

  open import Prim.Data.Unit
  kek : Hom ⊤ₜ Type₃
  kek tt = Type₂

  lol : {ℓ : Level} → Hom ⊤ₜ (Type ℓ)
  lol _ = Lift _ ⊤ₜ

-- module _ {ℓ-ob : Level → Level} {Ob : ob-sig ℓ-ob} (C : Quiver-on Ob) ⦃ _ : Comp C ⦄ where private
--   open Quiver-on C

--   Sqq : ℚuiver-on Ob
--   Sqq = ?
--   -- Sqq .ℚuiver-on.ℓ-sq = _
--   -- Sqq .ℚuiver-on.Quiverₕ = C
--   -- Sqq .ℚuiver-on.Quiverᵥ = C
--   -- Sqq .ℚuiver-on.Hom□ f g h k = f ∙ h ＝ g ∙ k

module DoubleCat {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} (C : ℚuiver-on Ob) where private
  open ℚuiver-on C

  record WildDoubleCat : Typeω where
    no-eta-equality
    field
      rᵥ : Refl _ Homᵥ
      cᵥ : Comp _ Homᵥ
      unit-lᵥ : Unit-i _ Homᵥ ⦃ rᵥ ⦄ ⦃ cᵥ ⦄ _＝_
      unit-rᵥ : Unit-o _ Homᵥ ⦃ rᵥ ⦄ ⦃ cᵥ ⦄ _＝_
      assocᵥ : Assoc _ Homᵥ ⦃ cᵥ ⦄ _＝_

      rₕ : Refl _ Homₕ
      cₕ : Comp _ Homₕ
      λₕ : Unit-i _ Homₕ ⦃ rₕ ⦄ ⦃ cₕ ⦄ λ f g → Hom□ f (refl ⦃ rᵥ ⦄) (refl ⦃ rᵥ ⦄) g
      ρₕ : Unit-o _ Homₕ ⦃ rₕ ⦄ ⦃ cₕ ⦄ λ f g → Hom□ f (refl ⦃ rᵥ ⦄) (refl ⦃ rᵥ ⦄) g
      αₕ : Assoc _ Homₕ ⦃ cₕ ⦄ λ f g → Hom□ f (refl ⦃ rᵥ ⦄) (refl ⦃ rᵥ ⦄) g

      r□  : ℝefl _ ⦃ rₕ ⦄ ⦃ rᵥ ⦄ Hom□
      c□  : ℂomp _ ⦃ cₕ ⦄ ⦃ cᵥ ⦄ Hom□
      ic□ : 𝕀nterchange _ ⦃ cₕ ⦄ ⦃ cᵥ ⦄ Hom□ ⦃ c□ ⦄ _＝_

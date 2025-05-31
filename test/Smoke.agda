{-# OPTIONS --safe #-}
module Smoke where

open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Double.Base
open import Notation.Double.Composition
open import Notation.Double.Interchange
open import Notation.Double.Reflexivity
open import Notation.Reflexivity
open import Notation.Strict
open import Notation.Unitality.Inner
open import Notation.Unitality.Outer

open import Foundations.Sigma.Base
open import Foundations.Path.Interface
open import Foundations.Pi.Interface

module _ {ℓa : Level} {A : Type ℓa} where
  Squares : ℚuiver-on (λ _ → A) _
  Squares .ℚuiver-on.Quiverₕ = Paths A
  Squares .ℚuiver-on.Quiverᵥ = Paths A
  Squares .ℚuiver-on.Sq p q r s = Pathᴾ (λ i → q i ＝ r i) p s

  instance
    sqre : ℝefl Squares lzero lzero
    sqre .ℝefl.reflₕ {f} i _ = f i
    sqre .ℝefl.reflᵥ {f} _ j = f j

module _ {ℓa : Level} {A : Type ℓa} {x y : A} {p : x ＝ y} where
  zook : Pathᴾ (λ i → p i ＝ p i) refl refl
  zook = reflₕ

  kooz : p ＝ p
  kooz = reflᵥ

open import Prim.Data.Sigma
Rels : (ℓ : Level) → Quiver-on (λ _ → Type ℓ) _
Rels ℓ .Quiver-on.Hom X Y = Σ (Type ℓ) λ S → (S → X) × (S → Y)

-- open import Prim.Equiv
-- instance
--   Rels-Comp : ∀{ℓ} → Comp _ (Rels ℓ)
--   Rels-Comp {ℓ} .Comp._∙_ (R , f , g) (S , h , k) = (Σ R (λ _ → S)) , (λ x₁ → f (x₁ .fst)) , λ z₁ → k (z₁ .snd)

--   Rels-Assoc : ∀{ℓ} → Assoc (Rels ℓ) λ A B → Lift _ {!!}
--   Rels-Assoc .Assoc.assoc f g h .lower = {!!}

module _ where private
  open Quiver-on Funs

  open import Prim.Data.Unit
  kek : Hom ⊤ Type₃
  kek tt = Type₂

  lol : {ℓ : Level} → Hom ⊤ (Type ℓ)
  lol _ = Lift _ ⊤

-- module _ {ℓ-ob : Level → Level} {Ob : ob-sig ℓ-ob} (C : Quiver-on Ob) ⦃ _ : Comp C ⦄ where private
--   open Quiver-on C

--   Sqq : ℚuiver-on Ob
--   Sqq = ?
--   -- Sqq .ℚuiver-on.ℓ-sq = _
--   -- Sqq .ℚuiver-on.Quiverₕ = C
--   -- Sqq .ℚuiver-on.Quiverᵥ = C
--   -- Sqq .ℚuiver-on.Hom□ f g h k = f ∙ h ＝ g ∙ k

module DoubleCat {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-sq : ℓ-sq-sig }(C : ℚuiver-on Ob ℓ-sq) where private
  open ℚuiver-on C

  record WildPseudoDoubleCat : Typeω where
    no-eta-equality
    field
      rᵥ : Reflω Quiverᵥ
      cᵥ : Compω Quiverᵥ
      unit-lᵥ : ∀{ℓx ℓy} → Unit-i Quiverᵥ Strict ℓx ℓy ⦃ rᵥ ⦄ ⦃ cᵥ ⦄
      unit-rᵥ : ∀{ℓx ℓy} → Unit-o Quiverᵥ Strict ℓx ℓy ⦃ rᵥ ⦄ ⦃ cᵥ ⦄
      assocᵥ : {ℓw ℓx ℓy ℓz : Level} → Assoc Quiverᵥ Strict ℓw ℓx ℓy ℓz ⦃ cᵥ ⦄ ⦃ cᵥ ⦄ ⦃ cᵥ ⦄ ⦃ cᵥ ⦄

      rₕ : Reflω Quiverₕ
      cₕ : Compω Quiverₕ
      λₕ : ∀{ℓx ℓy} → Unit-i Quiverₕ (mk-2-quiver λ x y → mk-quiver (λ f g → Sq f (refl ⦃ rᵥ ⦄) (refl ⦃  rᵥ ⦄) g)) ℓx ℓy ⦃ rₕ ⦄ ⦃ cₕ ⦄
      ρₕ : ∀{ℓx ℓy} → Unit-o Quiverₕ (mk-2-quiver λ x y → mk-quiver (λ f g → Sq f (refl ⦃ rᵥ ⦄) (refl ⦃  rᵥ ⦄) g)) ℓx ℓy ⦃ rₕ ⦄ ⦃ cₕ ⦄
      αₕ : ∀{ℓw ℓx ℓy ℓz} → Assoc Quiverₕ (mk-2-quiver λ x y → mk-quiver (λ f g → Sq f (refl ⦃ rᵥ ⦄) (refl ⦃ rᵥ ⦄) g)) ℓw ℓx ℓy ℓz ⦃ cₕ ⦄ ⦃ cₕ ⦄ ⦃ cₕ ⦄ ⦃ cₕ ⦄

      r□  : ∀{ℓx ℓy} → ℝefl C ℓx ℓy ⦃ rₕ ⦄ ⦃ rₕ ⦄ ⦃ rᵥ ⦄ ⦃ rᵥ ⦄
      c□  : ∀{ℓw ℓx ℓy ℓz ℓu ℓv} → ℂomp C ℓw ℓx ℓy ℓz ℓu ℓv ⦃ cₕ ⦄ ⦃ cᵥ ⦄
      ic□ : 𝕀nterchange C ⦃ cₕ ⦄ ⦃ cᵥ ⦄ ⦃ c□ ⦄ _＝_

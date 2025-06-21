{-# OPTIONS --safe #-}
module Notation.Refl where

open import Notation.Base
open import Notation.Lens.Bivariant
open import Notation.Lens.Contravariant
open import Notation.Lens.Covariant
open import Notation.Refl.Base public
open import Notation.Total
open import Notation.Wide

module _ {n : ℕ} {ℓ-obω : ℓ-sig n} {ℓ-homω : ℓ-sig² n}
  {C : Quiverω n ℓ-obω ℓ-homω} (open Quiverω C)
  {m : ℕ} {ℓ-obωᵈ : Levels n → ℓ-sig m} {ℓ-homωᵈ : Levels n → Levels n → ℓ-sig² m}
  {D : Quiverωᵈ C m ℓ-obωᵈ ℓ-homωᵈ} (open Quiverωᵈ D)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Reflωᵈ C D ⦄
  where instance

  ∫-Refl : Reflω (∫ D)
  ∫-Refl .refl .hom = refl
  ∫-Refl .refl .preserves = reflᵈ _

  Wide-Refl : {lsᵈ : Levels m} {t : ∀{ℓ} {x : Ob ℓ} → Ob[ x ] lsᵈ} → Reflω (Wide D lsᵈ t)
  Wide-Refl .refl .hom = refl
  Wide-Refl .refl .preserves = reflᵈ _

  Component-Refl : {ls : Levels n} {t : Ob ls} {lsᵈ : Levels m} → Reflω (Component D t lsᵈ) -- canonical way
  Component-Refl .refl = reflᵈ _

{-# INCOHERENT ∫-Refl Wide-Refl Component-Refl #-} -- TODO check if it's necessary


module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m : ℕ} {ℓ-obᶠ : Levels n → ℓ-sig m} {ℓ-homᶠ : Levels n → ℓ-sig² m}
  {F : {ls : Levels n} → Ob ls → Quiverω m (ℓ-obᶠ ls) (ℓ-homᶠ ls)}
  ⦃ _ : Reflω C ⦄
  where instance

  Disp⁺-Reflᵈ : ⦃ _ : Pushω C F ⦄ ⦃ _ : Lawful-Pushω C F ⦄ → Reflωᵈ C (Disp⁺ F)
  Disp⁺-Reflᵈ .reflᵈ _ = push-refl

  Disp⁻-Reflᵈ : ⦃ _ : Pullω C F ⦄ ⦃ _ : Lawful-Pullω C F ⦄ → Reflωᵈ C (Disp⁻ F)
  Disp⁻-Reflᵈ .reflᵈ _ = pull-refl


module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m : ℕ} {ℓ-obᶠ : Levels n → Levels n → ℓ-sig m} {ℓ-homᶠ : Levels n → Levels n → ℓ-sig² m}
  (F : {lxs lys : Levels n} {x : Ob lxs} {y : Ob lys} → Hom x y → Quiverω m (ℓ-obᶠ lxs lys) (ℓ-homᶠ lxs lys))
  ⦃ _ : Reflω C ⦄ ⦃ _ : Extendω C F ⦄ ⦃ _ : Lawful-Extendω C F ⦄
  where instance

  Disp±-Reflᵈ : Reflωᵈ C (Disp± F)
  Disp±-Reflᵈ .reflᵈ _ = extend-refl

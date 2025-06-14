{-# OPTIONS --safe #-}
module Notation.Refl where

open import Notation.Base
open import Notation.Lens.Bivariant
open import Notation.Lens.Contravariant
open import Notation.Lens.Covariant
open import Notation.Refl.Base public
open import Notation.Total
open import Notation.Wide

module _ {ℓ-ob ℓ-obᵈ : ℓ-sig¹} {ℓ-hom ℓ-homᵈ : ℓ-sig²}
  {C : Quiverω ℓ-ob ℓ-hom} (open Quiverω C) ⦃ _ : Reflω C ⦄
  {D : Quiverωᵈ C ℓ-obᵈ ℓ-homᵈ} (open Quiverωᵈ D) ⦃ _ : Reflωᵈ D ⦄ where instance

  ∫-Refl : Reflω (∫ D)
  ∫-Refl .refl .hom = refl
  ∫-Refl .refl .preserves = reflᵈ

  Wide-Refl : {t : ∀{ℓ} {x : Ob ℓ} → Ob[ x ]} → Reflω (Wide D t)
  Wide-Refl .refl .hom = refl
  Wide-Refl .refl .preserves = reflᵈ

  Component-Refl : ∀{ℓ} {t : Ob ℓ} → Reflω (D $ωᵈ t) -- canonical way
  Component-Refl .refl = reflᵈ

{-# INCOHERENT ∫-Refl Wide-Refl Component-Refl #-} -- TODO check if it's necessary


module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom ℓ-obᶠ : ℓ-sig²} {ℓ-homᶠ : ℓ-sig³}
  {C : Quiverω ℓ-ob ℓ-hom} (open Quiverω C) ⦃ _ : Reflω C ⦄
  {F : ∀{ℓt} (t : Ob ℓt) → Quiverω (ℓ-obᶠ ℓt) (ℓ-homᶠ ℓt)} where instance

  Disp⁺-Reflᵈ : ⦃ _ : Pushω C F ⦄ ⦃ _ : Lawful-Pushω C F ⦄ → Reflωᵈ (Disp⁺ F)
  Disp⁺-Reflᵈ .reflᵈ = push-refl

  Disp⁻-Reflᵈ : ⦃ _ : Pullω C F ⦄ ⦃ _ : Lawful-Pullω C F ⦄ → Reflωᵈ (Disp⁻ F)
  Disp⁻-Reflᵈ .reflᵈ = pull-refl


module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom : ℓ-sig²} {ℓ-obᶠ : ℓ-sig³} {ℓ-homᶠ : ℓ-sig⁴}
  {C : Quiverω ℓ-ob ℓ-hom} (open Quiverω C) ⦃ _ : Reflω C ⦄
  {F : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (p : Hom x y) → Quiverω (ℓ-obᶠ ℓx ℓy) (ℓ-homᶠ ℓx ℓy)}
  ⦃ _ : Extendω C F ⦄ ⦃ _ : Lawful-Extendω C F ⦄ where instance
  private module F {ℓx} {ℓy} x y p = Quiverω (F {ℓx} {ℓy} {x} {y} p)

  Disp±-Reflᵈ : Reflωᵈ (Disp± F)
  Disp±-Reflᵈ .reflᵈ = extend-refl

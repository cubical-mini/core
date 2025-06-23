{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Contravariant where

open import Foundations.Quiver.Base

open import Notation.Lens.Contravariant
open import Notation.Refl

module _ {n ℓ-ob ℓ-hom} {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m} {ℓ-obᶠ : Levels n → ℓ-sig m} {ℓ-homᶠ : Levels n → ℓ-sig² m}
  (F : ∀{ls} → Ob ls → Quiverω m (ℓ-obᶠ ls) (ℓ-homᶠ ls))
  where
  private module F {ls} x = Quiverω (F {ls} x)

  Disp⁻ : ⦃ _ : Pullω C F ⦄ → Quiverωᵈ C m _ _
  Disp⁻ .Quiverωᵈ.Ob[_] = F.Ob
  Disp⁻ .has-quiver-onωᵈ .Quiver-onωᵈ.Hom[_] {x} p u v = F.Hom x u (pull p v)


module _ {n ℓ-ob ℓ-hom} {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m} {ℓ-obᶠ : Levels n → ℓ-sig m} {ℓ-homᶠ : Levels n → ℓ-sig² m}
  {F : ∀{ls} → Ob ls → Quiverω m (ℓ-obᶠ ls) (ℓ-homᶠ ls)}
  ⦃ _ : Reflω C ⦄ where instance

  Disp⁻-Reflᵈ : ⦃ _ : Pullω C F ⦄ ⦃ _ : Lawful-Pullω C F ⦄ → Reflωᵈ C (Disp⁻ F)
  Disp⁻-Reflᵈ .reflᵈ _ = pull-refl
  {-# INCOHERENT Disp⁻-Reflᵈ #-} -- TODO check

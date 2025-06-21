{-# OPTIONS --safe #-}
module Notation.Lens.Contravariant where

open import Prim.Type

open import Notation.Base
open import Notation.Lens.Contravariant.Base   public
open import Notation.Lens.Contravariant.Lawful public
open import Notation.Refl.Base

module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m : ℕ} {ℓ-obᶠ : Levels n → ℓ-sig m} {ℓ-homᶠ : Levels n → ℓ-sig² m}
  (F : {ls : Levels n} → Ob ls → Quiverω m (ℓ-obᶠ ls) (ℓ-homᶠ ls))
  where
  private module F {ls} x = Quiverω (F {ls} x)

  Disp⁻ : ⦃ _ : Pullω C F ⦄ → Quiverωᵈ C m _ _
  Disp⁻ .Quiverωᵈ.Ob[_] = F.Ob
  Disp⁻ .Quiverωᵈ.Hom[_] {x} p u v = F.Hom x u (pull p v)

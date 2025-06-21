{-# OPTIONS --safe #-}
module Notation.Lens.Covariant where

open import Prim.Type

open import Notation.Base
open import Notation.Lens.Covariant.Base   public
open import Notation.Lens.Covariant.Lawful public
open import Notation.Refl.Base

module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m : ℕ} {ℓ-obᶠ : Levels n → ℓ-sig m} {ℓ-homᶠ : Levels n → ℓ-sig² m}
  (F : {ls : Levels n} → Ob ls → Quiverω m (ℓ-obᶠ ls) (ℓ-homᶠ ls))
  where
  private module F {ls} x = Quiverω (F {ls} x)

  Disp⁺ : ⦃ _ : Pushω C F ⦄ → Quiverωᵈ C m _ _
  Disp⁺ .Quiverωᵈ.Ob[_] = F.Ob
  Disp⁺ .Quiverωᵈ.Hom[_] {y} p u v = F.Hom y (push p u) v

{-# OPTIONS --safe #-}
module Notation.Lens.Bivariant where

open import Prim.Type

open import Notation.Base
open import Notation.Lens.Bivariant.Base   public
open import Notation.Lens.Bivariant.Lawful public
open import Notation.Refl.Base

module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m : ℕ} {ℓ-obᶠ : Levels n → Levels n → ℓ-sig m} {ℓ-homᶠ : Levels n → Levels n → ℓ-sig² m}
  (F : {lxs lys : Levels n} {x : Ob lxs} {y : Ob lys} → Hom x y → Quiverω m (ℓ-obᶠ lxs lys) (ℓ-homᶠ lxs lys))
  ⦃ _ : Reflω C ⦄
  where
  private module F {lxs} {lys} x y p = Quiverω (F {lxs} {lys} {x} {y} p)

  Disp± : ⦃ _ : Extendω C F ⦄ → Quiverωᵈ C m _ _
  Disp± .Quiverωᵈ.Ob[_] t = F.Ob t t refl
  Disp± .Quiverωᵈ.Hom[_] {x} {y} p u v = F.Hom x y p (extend-l p u) (extend-r p v)

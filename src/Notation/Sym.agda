{-# OPTIONS --safe #-}
module Notation.Sym where

open import Foundations.Quiver.Base

module _ {n ℓ-ob ℓ-hom} (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C) where

  record Sym lxs lys : Type (ℓ-ob lxs ⊔ ℓ-ob lys ⊔ ℓ-hom lxs lys ⊔ ℓ-hom lys lxs) where
    no-eta-equality
    field sym : {x : Ob lxs} {y : Ob lys} → Hom x y → Hom y x

  Symω : Typeω
  Symω = ∀ {lxs lys} → Sym lxs lys

open Sym ⦃ ... ⦄ public
{-# DISPLAY Sym.sym _ p = sym p #-}


module _ {n ℓ-ob ℓ-hom} (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C)
  {m ℓ-obᵈ ℓ-homᵈ} (D : Quiverωᵈ C m ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D)
  ⦃ _ : Symω C ⦄ where

  record Symᵈ lxs lys lxsᵈ lysᵈ : Type
    ( ℓ-ob lxs ⊔ ℓ-ob lys ⊔ ℓ-hom lxs lys ⊔ ℓ-obᵈ lxs lxsᵈ
    ⊔ ℓ-obᵈ lys lysᵈ ⊔ ℓ-homᵈ lxs lys lxsᵈ lysᵈ ⊔ ℓ-homᵈ lys lxs lysᵈ lxsᵈ) where
    no-eta-equality
    field symᵈ : {x : Ob lxs} {y : Ob lys} {f : Hom x y}
                 {x′ : Ob[ x ] lxsᵈ} {y′ : Ob[ y ] lysᵈ}
               → Hom[ f ] x′ y′ → Hom[ sym f ] y′ x′

  Symωᵈ : Typeω
  Symωᵈ = ∀ {lxs lys lxsᵈ lysᵈ} → Symᵈ lxs lys lxsᵈ lysᵈ

open Symᵈ ⦃ ... ⦄ public
{-# DISPLAY Symᵈ.symᵈ _ p = symᵈ p #-}

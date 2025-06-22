{-# OPTIONS --safe #-}
module Notation.Comp.Base where

open import Notation.Base

module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C) where

  record Comp (lxs lys lzs : Levels n) : Type
    ( ℓ-ob lxs ⊔ ℓ-ob lys ⊔ ℓ-ob lzs ⊔ ℓ-hom lxs lys
    ⊔ ℓ-hom lxs lzs ⊔ ℓ-hom lys lzs) where
    no-eta-equality
    infixl 90 _∙_
    field _∙_ : {x : Ob lxs} {y : Ob lys} {z : Ob lzs}
              → Hom x y → Hom y z → Hom x z

  Compω : Typeω
  Compω = ∀{lxs lys lzs} → Comp lxs lys lzs

open Comp ⦃ ... ⦄ public
{-# DISPLAY Comp._∙_ _ f g = f ∙ g #-}


module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C)
  {m : ℕ} {ℓ-obᵈ : Levels n → ℓ-sig m} {ℓ-homᵈ : Levels n → Levels n → ℓ-sig² m}
  (D : Quiverωᵈ C m ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D)
  ⦃ _ : Compω C ⦄
  where

  record Compᵈ (lxs lys lzs : Levels n) (lxsᵈ lysᵈ lzsᵈ : Levels m) : Type
    ( ℓ-ob lxs ⊔ ℓ-ob lys ⊔ ℓ-ob lzs ⊔ ℓ-hom lxs lys ⊔ ℓ-hom lys lzs
    ⊔ ℓ-obᵈ lxs lxsᵈ ⊔ ℓ-obᵈ lys lysᵈ ⊔ ℓ-obᵈ lzs lzsᵈ ⊔ ℓ-homᵈ lxs lys lxsᵈ lysᵈ
    ⊔ ℓ-homᵈ lxs lzs lxsᵈ lzsᵈ ⊔ ℓ-homᵈ lys lzs lysᵈ lzsᵈ) where
    no-eta-equality
    infixl 90 _∙ᵈ_
    field
      _∙ᵈ_ : {x : Ob lxs} {y : Ob lys} {z : Ob lzs}
             {f : Hom x y} {g : Hom y z}
             {x′ : Ob[ x ] lxsᵈ} {y′ : Ob[ y ] lysᵈ} {z′ : Ob[ z ] lzsᵈ}
           → Hom[ f ] x′ y′ → Hom[ g ] y′ z′ → Hom[ f ∙ g ] x′ z′

  Compωᵈ : Typeω
  Compωᵈ = ∀{lxs lys lzs lxsᵈ lysᵈ lzsᵈ} → Compᵈ lxs lys lzs lxsᵈ lysᵈ lzsᵈ

open Compᵈ ⦃ ... ⦄ public
{-# DISPLAY Compᵈ._∙ᵈ_ _ f g = f ∙ᵈ g #-}

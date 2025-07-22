{-# OPTIONS --safe #-}
module Notation.Comp where

open import Foundations.Quiver.Base

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom)) where

  record HComp lxs lys lzs : Type
    ( ℓ-ob lxs ⊔ ℓ-ob lys ⊔ ℓ-ob lzs ⊔ ℓ-hom lxs lys
    ⊔ ℓ-hom lxs lzs ⊔ ℓ-hom lys lzs) where
    no-eta-equality
    infixl 90 _∙_
    field _∙_ : {x : Ob lxs} {y : Ob lys} {z : Ob lzs}
              → Hom x y → Hom y z → Hom x z

  HCompω : Typeω
  HCompω = ∀{lxs lys lzs} → HComp lxs lys lzs

open HComp ⦃ ... ⦄ public
{-# DISPLAY HComp._∙_ _ f g = f ∙ g #-}


module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {m′ ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  (D : HQuiver-onωᵈ C m′ Ob[_] ℓ-homᵈ) (open Quiver-onωᵈ D renaming (Het[_] to Hom[_]))
  ⦃ _ : HCompω C ⦄ where

  record HCompᵈ lxs lys lzs lxsᵈ lysᵈ lzsᵈ : Type
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

  HCompωᵈ : Typeω
  HCompωᵈ = ∀{lxs lys lzs lxsᵈ lysᵈ lzsᵈ} → HCompᵈ lxs lys lzs lxsᵈ lysᵈ lzsᵈ

open HCompᵈ ⦃ ... ⦄ public
{-# DISPLAY HCompᵈ._∙ᵈ_ _ f g = f ∙ᵈ g #-}

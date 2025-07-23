{-# OPTIONS --safe #-}
module Notation.Comp where

open import Foundations.Quiver.Base

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom)) where

  record HComp : Typeω where
    no-eta-equality
    infixl 90 _∙_
    field _∙_ : ∀{lxs lys lzs} {x : Ob lxs} {y : Ob lys} {z : Ob lzs}
              → Hom x y → Hom y z → Hom x z

open HComp ⦃ ... ⦄ public
{-# DISPLAY HComp._∙_ _ f g = f ∙ g #-}


module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {m′ ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  (D : HQuiver-onωᵈ C m′ Ob[_] ℓ-homᵈ) (open Quiver-onωᵈ D renaming (Het[_] to Hom[_]))
  ⦃ _ : HComp C ⦄ where

  record HCompᵈ : Typeω where
    no-eta-equality
    infixl 90 _∙ᵈ_
    field
      _∙ᵈ_ : ∀{lxs lys lzs lxsᵈ lysᵈ lzsᵈ}
             {x : Ob lxs} {y : Ob lys} {z : Ob lzs}
             {f : Hom x y} {g : Hom y z}
             {x′ : Ob[ x ] lxsᵈ} {y′ : Ob[ y ] lysᵈ} {z′ : Ob[ z ] lzsᵈ}
           → Hom[ f ] x′ y′ → Hom[ g ] y′ z′ → Hom[ f ∙ g ] x′ z′

open HCompᵈ ⦃ ... ⦄ public
{-# DISPLAY HCompᵈ._∙ᵈ_ _ f g = f ∙ᵈ g #-}

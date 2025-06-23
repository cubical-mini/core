{-# OPTIONS --safe #-}
module Notation.Assoc where

open import Foundations.Quiver.Base

open import Notation.Comp

module _ {n ℓ-ob ℓ-hom} (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C)
  {ℓ-hom₂ : ℓ-sig² n} (C₂ : 2-Quiver-onω C ℓ-hom₂)
  ⦃ _ : Compω C ⦄ where
  private open module C₂ {lxs} {lys} {x} {y} = Quiver-onω (C₂ {lxs} {lys} x y)
            renaming (Hom to 2-Hom)

  record Assoc lws lxs lys lzs : Type
    ( ℓ-ob lws ⊔ ℓ-ob lxs ⊔ ℓ-ob lys ⊔ ℓ-ob lzs ⊔ ℓ-hom lws lxs
    ⊔ ℓ-hom lxs lys ⊔ ℓ-hom lys lzs ⊔ ℓ-hom₂ lws lzs) where
    no-eta-equality
    field assoc : {w : Ob lws} {x : Ob lxs} {y : Ob lys} {z : Ob lzs}
                  {f : Hom w x} {g : Hom x y} {h : Hom y z}
                → 2-Hom (f ∙ (g ∙ h)) ((f ∙ g) ∙ h)

  Assocω : Typeω
  Assocω = ∀{lws lxs lys lzs} → Assoc lws lxs lys lzs

open Assoc ⦃ ... ⦄ public
{-# DISPLAY Assoc.assoc _ = assoc #-}

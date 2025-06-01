{-# OPTIONS --safe #-}
module Notation.Displayed.Reflexivity where

open import Prim.Type

open import Notation.Base
open import Notation.Displayed.Base
open import Notation.Reflexivity

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  {ℓ-obᵈ : ℓ-ob-sig} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ} {ℓ-homᵈ : ℓ-hom-sig} (D : Quiver-onᵈ C Ob[_] ℓ-homᵈ) (open Quiver-onᵈ D)
  ⦃ _ : Reflω C ⦄
  where
  
  record Reflᵈ ℓ : Type (ℓ-ob ℓ l⊔ ℓ-obᵈ ℓ l⊔ ℓ-homᵈ ℓ ℓ) where
    no-eta-equality
    field reflᵈ : {x : Ob ℓ} {x′ : Ob[ x ]} → Hom[ refl ] x′ x′

  Reflᵈω : Typeω
  Reflᵈω = {ℓ : Level} → Reflᵈ ℓ

open Reflᵈ ⦃ ... ⦄ public

{-# DISPLAY Reflᵈ.reflᵈ _ = reflᵈ #-}

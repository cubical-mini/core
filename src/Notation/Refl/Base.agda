{-# OPTIONS --safe #-}
module Notation.Refl.Base where

open import Prim.Type

open import Notation.Base

module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom : ℓ-sig²}
  (C : Quiverω ℓ-ob ℓ-hom) (open Quiverω C) where

  record Refl ℓ : Type (ℓ-ob ℓ ⊔ ℓ-hom ℓ ℓ) where
    no-eta-equality
    field refl : {x : Ob ℓ} → Hom x x

  Reflω = ∀ {ℓ} → Refl ℓ

open Refl ⦃ ... ⦄ public
{-# DISPLAY Refl.refl _ = refl #-}


module _ {ℓ-ob ℓ-obᵈ : ℓ-sig¹} {ℓ-hom ℓ-homᵈ : ℓ-sig²}
  {C : Quiverω ℓ-ob ℓ-hom} (open Quiverω C) ⦃ _ : Reflω C ⦄
  (D : Quiverωᵈ C ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D) where

  record Reflᵈ ℓ : Typeω where
    no-eta-equality
    field reflᵈ : {x : Ob ℓ} {x′ : Ob[ x ]} → Hom[ refl ] x′ x′

  Reflωᵈ = ∀ {ℓ} → Reflᵈ ℓ

open Reflᵈ ⦃ ... ⦄ public
{-# DISPLAY Reflᵈ.reflᵈ _ = reflᵈ #-}


-- displayed quiver over a reflexive quiver begets a family of _small_ quivers
module _ {ℓ-ob ℓ-obᵈ : ℓ-sig¹} {ℓ-hom ℓ-homᵈ : ℓ-sig²}
  {C : Quiverω ℓ-ob ℓ-hom} (open Quiverω C) ⦃ _ : Reflω C ⦄
  (D : Quiverωᵈ C ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D) where
  module _ {ℓ} (t : Ob ℓ) where
    _$ωᵈ_ : Quiverω (λ _ → ℓ-obᵈ ℓ) (λ _ _ → ℓ-homᵈ ℓ ℓ)
    _$ωᵈ_ .Ob _ = Ob[ t ]
    _$ωᵈ_ .Hom  = Hom[ refl ]

{-# OPTIONS --safe #-}
module Quiver.Base where

open import Prim.Type

ℓ-sig¹ = Level → Level
ℓ-sig² = Level → Level → Level

record Quiverω (ℓ-ob : ℓ-sig¹) (ℓ-hom : ℓ-sig²) : Typeω where
  constructor mk-quiverω
  no-eta-equality
  field
    Ob   : ∀ ℓ → Type (ℓ-ob ℓ)
    Hom  : ∀{ℓx ℓy} → Ob ℓx → Ob ℓy → Type (ℓ-hom ℓx ℓy)
    refl : ∀{ℓ} {x : Ob ℓ} → Hom x x
{-# INLINE mk-quiverω #-}


module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom : ℓ-sig²} (C : Quiverω ℓ-ob ℓ-hom) (open Quiverω C) where
  record Quiverωᵈ (ℓ-obᵈ : ℓ-sig¹) (ℓ-homᵈ : ℓ-sig²) : Typeω where
    constructor mk-quiverωᵈ
    no-eta-equality
    field
      Ob[_]    : ∀{ℓ} → Ob ℓ → Type (ℓ-obᵈ ℓ)
      Hom[_]   : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} → Hom x y → Ob[ x ] → Ob[ y ] → Type (ℓ-homᵈ ℓx ℓy)
      reflᵈ    : ∀{ℓ} {x : Ob ℓ} {x′ : Ob[ x ]} → Hom[ refl ] x′ x′
  {-# INLINE mk-quiverωᵈ #-}

-- displayed quiver begets a family of quivers
module _ {ℓ-ob ℓ-obᵈ : ℓ-sig¹} {ℓ-hom ℓ-homᵈ : ℓ-sig²} {C : Quiverω ℓ-ob ℓ-hom} (open Quiverω C) (D : Quiverωᵈ C ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D) where
  module _ {ℓ} (t : Ob ℓ) where
    _$ωᵈ_ : Quiverω (λ _ → ℓ-obᵈ ℓ) (λ _ _ → ℓ-homᵈ ℓ ℓ)
    _$ωᵈ_ .Ob _ = Ob[ t ]
    _$ωᵈ_ .Hom  = Hom[ refl ]
    _$ωᵈ_ .refl = reflᵈ

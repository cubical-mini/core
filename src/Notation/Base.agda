{-# OPTIONS --safe #-}
module Notation.Base where

open import Prim.Type

ℓ-sig⁰ = Level
ℓ-sig¹ = Level → ℓ-sig⁰
ℓ-sig² = Level → ℓ-sig¹
ℓ-sig³ = Level → ℓ-sig²
ℓ-sig⁴ = Level → ℓ-sig³

record Quiverω (ℓ-ob : ℓ-sig¹) (ℓ-hom : ℓ-sig²) : Typeω where
  constructor mk-quiverω
  no-eta-equality
  field
    Ob   : ∀ ℓ → Type (ℓ-ob ℓ)
    Hom  : ∀{ℓx ℓy} → Ob ℓx → Ob ℓy → Type (ℓ-hom ℓx ℓy)
{-# INLINE mk-quiverω #-}

module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom : ℓ-sig²} (C : Quiverω ℓ-ob ℓ-hom) (open Quiverω C) where
  record Quiverωᵈ (ℓ-obᵈ : ℓ-sig¹) (ℓ-homᵈ : ℓ-sig²) : Typeω where
    constructor mk-quiverωᵈ
    no-eta-equality
    field
      Ob[_]  : ∀{ℓ} → Ob ℓ → Type (ℓ-obᵈ ℓ)
      Hom[_] : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} → Hom x y → Ob[ x ] → Ob[ y ] → Type (ℓ-homᵈ ℓx ℓy)
  {-# INLINE mk-quiverωᵈ #-}

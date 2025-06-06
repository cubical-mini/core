{-# OPTIONS --safe #-}
module Quiver.Total where

open import Prim.Data.Sigma public
open import Prim.Type

open import Quiver.Base

module _ {ℓ-ob ℓ-obᵈ : ℓ-sig¹} {Ob : ∀ ℓ → Type (ℓ-ob ℓ)} (Ob[_] : ∀{ℓ} → Ob ℓ → Type (ℓ-obᵈ ℓ)) where
  ΣOb : (ℓ : Level) → Type (ℓ-ob ℓ ⊔ ℓ-obᵈ ℓ)
  ΣOb ℓ = Σ (Ob ℓ) Ob[_]

module _ {ℓ-ob ℓ-obᵈ : ℓ-sig¹} {ℓ-hom ℓ-homᵈ : ℓ-sig²} (C : Quiverω ℓ-ob ℓ-hom) (open Quiverω C)
  (D : Quiverωᵈ C ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D)
  {ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} where
  infixr 40 _,⃗_
  record ΣHom (x′ : Ob[ x ]) (y′ : Ob[ y ]) : Type (ℓ-hom ℓx ℓy ⊔ ℓ-homᵈ ℓx ℓy) where
    constructor _,⃗_
    field
      hom       : Hom x y
      preserves : Hom[ hom ] x′ y′
  open ΣHom public


module _ {ℓ-ob ℓ-obᵈ : ℓ-sig¹} {ℓ-hom ℓ-homᵈ : ℓ-sig²} {C : Quiverω ℓ-ob ℓ-hom} (open Quiverω C)
  (D : Quiverωᵈ C ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D) where
  ∫ : Quiverω (λ ℓ → ℓ-ob ℓ ⊔ ℓ-obᵈ ℓ) (λ ℓx ℓy → ℓ-hom ℓx ℓy ⊔ ℓ-homᵈ ℓx ℓy)
  ∫ .Ob        = ΣOb (λ {ℓ} → Ob[_] {ℓ})
  ∫ .Hom x′ y′ = ΣHom C D (x′ .snd) (y′ .snd)
  ∫ .refl .hom = refl
  ∫ .refl .preserves = reflᵈ

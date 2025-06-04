{-# OPTIONS --safe #-}
module Notation.Displayed.Base where

open import Prim.Type

open import Notation.Base

ob-sigᵈ : {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) (ℓ-obᵈ : ℓ-ob-sig) → Typeω
ob-sigᵈ Ob ℓ-obᵈ = ∀{ℓ} → Ob ℓ → Type (ℓ-obᵈ ℓ)
{-# INLINE ob-sigᵈ #-}

hom-sigᵈ
  : {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) {ℓ-hom : ℓ-hom-sig} (Hom : hom-sig Ob ℓ-hom)
    {ℓ-obᵈ : ℓ-ob-sig} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ) (ℓ-homᵈ : ℓ-hom-sig)
  → Typeω
hom-sigᵈ Ob Hom Ob[_] ℓ-homᵈ = ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} → Hom x y → Ob[ x ] → Ob[ y ] → Type (ℓ-homᵈ ℓx ℓy)
{-# INLINE hom-sigᵈ #-}

record Quiver-onᵈ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom)
  {ℓ-obᵈ : ℓ-ob-sig} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ) (ℓ-homᵈ : ℓ-hom-sig) : Typeω where
  constructor mk-quiverᵈ
  no-eta-equality
  open Quiver-on C
  field Hom[_] : hom-sigᵈ Ob Hom Ob[_] ℓ-homᵈ
{-# INLINE mk-quiverᵈ #-}

record Small-quiver-onᵈ {ℓo : Level} {Ob : Type ℓo} {ℓh : Level} (C : Small-quiver-on Ob ℓh)
  {ℓoᵈ : Level} (Ob[_] : Ob → Type ℓoᵈ) (ℓhᵈ : Level) : Type (ℓo l⊔ ℓh l⊔ ℓoᵈ l⊔ lsuc ℓhᵈ) where
  constructor mk-small-quiverᵈ
  no-eta-equality
  open Small-quiver-on C
  field Hom[_] : {x y : Ob} → Hom x y → Ob[ x ] → Ob[ y ] → Type ℓhᵈ
{-# INLINE mk-small-quiverᵈ #-}

Enlargeᵈ : ∀{ℓo ℓh ℓoᵈ ℓhᵈ} {Ob : Type ℓo} {C : Small-quiver-on Ob ℓh} {Ob[_] : Ob → Type ℓoᵈ}
         → Small-quiver-onᵈ C Ob[_] ℓhᵈ → Quiver-onᵈ (Enlarge C) (λ {_} → Ob[_]) λ _ _ → ℓhᵈ
Enlargeᵈ d .Quiver-onᵈ.Hom[_] = d .Small-quiver-onᵈ.Hom[_]

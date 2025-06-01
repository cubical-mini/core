{-# OPTIONS --safe #-}
module Notation.Invertibility.Retraction where

open import Prim.Data.Unit
open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Displayed.Reflexivity
open import Notation.Idempotent
open import Notation.Reflexivity
open import Notation.Split
open import Notation.Strict

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓx ℓy : Level} ⦃ _ : Refl C ℓy ⦄ ⦃ _ : Comp C ℓy ℓx ℓy ⦄ where

  record Split-mono {x : Ob ℓx} {y : Ob ℓy} (s : Hom y x) : Type (ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓy ℓy) where
    no-eta-equality
    field
      retraction      : Hom x y
      retraction-cell : retraction retraction-of s

open Split-mono public

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  Split-monosᵈ : Quiver-onᵈ C (λ _ → ⊤) (λ ℓx ℓy → ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓy ℓx)
  Split-monosᵈ .Quiver-onᵈ.Hom[_] f _ _ = Split-mono f

  instance
    Split-mono-reflᵈ : {ℓ : Level}
                       ⦃ _ : {ℓ : Level} {x : Ob ℓ} → Idem C Strict {x = x} refl ⦄
                     → Reflᵈ C Split-monosᵈ ℓ
    Split-mono-reflᵈ .reflᵈ .retraction      = refl
    Split-mono-reflᵈ .reflᵈ .retraction-cell = idem

  infix 10 _↣!_
  _↣!_ : ∀ {ℓx ℓy}(y : Ob ℓy) (x : Ob ℓx) → Type (ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓy ℓy)
  y ↣! x = Total-hom C Split-monosᵈ {x = y} {y = x} tt tt

{-# DISPLAY Total-hom {_} {_} {_} _ {_} {_} {_} Split-monosᵈ {_} {_} {x} {y} _ _ = x ↣! y #-}

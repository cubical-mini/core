{-# OPTIONS --safe #-}
module Notation.Terminal.Base where

open import Prim.Type

open import Notation.Base

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  where

  record Weak-Terminal ℓt ℓ : Type (ℓ-ob ℓt l⊔ ℓ-ob ℓ l⊔ ℓ-hom ℓ ℓt) where
    no-eta-equality
    constructor mk-terminal
    field
      ⊤      : Ob ℓt
      !      : {x : Ob ℓ} → Hom x ⊤
      !-cell : {x : Ob ℓ} (h : Hom x ⊤) → 2-Hom ! h

open Weak-Terminal ⦃ ... ⦄ public
  using (⊤ ; ! ; !-cell)

{-# DISPLAY Weak-Terminal.⊤ _ = ⊤ #-}
{-# DISPLAY Weak-Terminal.! _ = ! #-}
{-# DISPLAY Weak-Terminal.!-cell _ h = !-cell h #-}

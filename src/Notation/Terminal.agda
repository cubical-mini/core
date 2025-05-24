{-# OPTIONS --safe #-}
module Notation.Terminal where

open import Prim.Type

open import Notation.Base

-- coherent, can be used for instance resolution
module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (CC : 2-Quiver-on C) (open 2-Quiver-on CC) where

  record Terminal ℓt ℓ : Type (ℓ-ob ℓt l⊔ ℓ-ob ℓ l⊔ ℓ-hom ℓ ℓt) where
    no-eta-equality
    constructor mk-terminal
    field
      ⊤      : Ob ℓt
      !      : {x : Ob ℓ} → Hom x ⊤
      !-cell : {x : Ob ℓ} (h : Hom x ⊤) → 2-Hom h !

open Terminal ⦃ ... ⦄ public
  using (⊤ ; ! ; !-cell)

{-# DISPLAY Terminal.⊤ _ = ⊤ #-}
{-# DISPLAY Terminal.! _ = ! #-}
{-# DISPLAY Terminal.!-cell _ h = !-cell h #-}

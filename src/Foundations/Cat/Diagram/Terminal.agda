{-# OPTIONS --safe #-}
module Control.Diagram.Terminal where

open import Prim.Kan
open import Prim.Type

open import Control.Composition
open import Control.Structures.Quiver

module _ (C : Quiver) {ℓt : Level} where
  open Quiver C

  is-terminal : ∀ {ℓ} → Ob ℓt → Type (ob-lvl ℓ ⊔ hom-lvl ℓ ℓt)
  is-terminal {ℓ} t = (x : Ob ℓ) → is-contr (Hom x t)

  record Terminal : Typeω where
    no-eta-equality
    constructor mk-terminal
    field
      ⊤               : Ob ℓt
      has-is-terminal : ∀ {ℓ} → is-terminal {ℓ} ⊤

    ! : ∀ {ℓ} {x : Ob ℓ} → Hom x ⊤
    ! {x} = has-is-terminal x .centre

{-# INLINE mk-terminal #-}
open Terminal ⦃ ... ⦄ public
  using (⊤; !)

{-# DISPLAY Terminal.⊤ _ = ⊤ #-}

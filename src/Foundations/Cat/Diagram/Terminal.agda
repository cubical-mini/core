{-# OPTIONS --safe #-}
module Foundations.Cat.Diagram.Terminal where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Foundations.Cat.Composition

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  (Ob  : (ℓ : Level) → Type (ob-lvl ℓ))
  (Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy))
  {ℓt : Level}
  where

  is-terminal : {ℓ : Level} → Ob ℓt → Type (ob-lvl ℓ l⊔ hom-lvl ℓ ℓt)
  is-terminal {ℓ} t = (x : Ob ℓ) → is-contr (Hom x t)

  record Terminal : Typeω where
    no-eta-equality
    constructor mk-terminal
    field
      ⊤               : Ob ℓt
      has-is-terminal : {ℓ : Level} → is-terminal {ℓ} ⊤

    ! : {ℓ : Level} {x : Ob ℓ} → Hom x ⊤
    ! {x} = has-is-terminal x .centre

{-# INLINE mk-terminal #-}
open Terminal ⦃ ... ⦄ public
  using (⊤; !)

{-# DISPLAY Terminal.⊤ _ = ⊤ #-}

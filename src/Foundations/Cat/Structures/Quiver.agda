{-# OPTIONS --safe #-}
module Foundations.Cat.Structures.Quiver where

open import Foundations.Prim.Type

record Quiver : Typeω where
  constructor mk-quiver
  no-eta-equality
  field
    {ob-lvl} : Level → Level
    {hom-lvl} : Level → Level → Level
    Ob : (ℓ : Level) → Type (ob-lvl ℓ)
    Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy)

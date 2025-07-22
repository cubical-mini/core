{-# OPTIONS --safe --erased-cubical #-}
module Foundations.Quiver.Discrete.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete.Base

open import Notation.Comp
open import Notation.Sym
open import Notation.Refl

instance
  Disc-Refl : ∀{ℓ} {A : Type ℓ} → Reflω (Disc A)
  Disc-Refl .refl {x} _ = x

  Disc-Sym : ∀{ℓ} {A : Type ℓ} → Symω (Disc A)
  Disc-Sym .sym p i = p (~ i)

  -- TODO
  -- Disc-HComp : ∀{ℓ} {A : Type ℓ} → HCompω (Disc A)
  -- Disc-HComp ._∙_ p q = {!!}

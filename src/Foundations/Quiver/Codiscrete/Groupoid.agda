{-# OPTIONS --safe #-}
module Foundations.Quiver.Codiscrete.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Codiscrete.Base

open import Notation.Comp
open import Notation.Refl
open import Notation.Sym

instance
  Codisc-Refl : ∀{ℓ} {A : Type ℓ} → Reflω (Codisc A)
  Codisc-Refl .refl = tt

  Codisc-Sym : ∀{ℓ} {A : Type ℓ} → Symω (Codisc A)
  Codisc-Sym .sym _ = tt

  Codisc-HComp : ∀{ℓ} {A : Type ℓ} → HCompω (Codisc A)
  Codisc-HComp ._∙_ _ _ = tt

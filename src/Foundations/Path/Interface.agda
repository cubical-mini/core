{-# OPTIONS --safe #-}
module Foundations.Path.Interface where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Strict
open import Notation.Symmetry

open import Foundations.Path.Base
  public
  renaming ( refl to reflₚ
           ; sym  to symₚ
           ; _∙_  to _∙ₚ_

           ; Square to Squareₚ
           )

instance
  Refl-Path : {ℓ : Level} {A : Type ℓ} → Refl (Paths A) lzero
  Refl-Path .refl = reflₚ

  Sym-Path : {ℓ : Level} {A : Type ℓ} → Symmetry (Paths A) lzero lzero
  Sym-Path .sym = symₚ

  Comp-Path : {ℓ : Level} {A : Type ℓ} → Comp (Paths A) lzero lzero lzero
  Comp-Path ._∙_ = _∙ₚ_
{-# INCOHERENT Refl-Path Sym-Path Comp-Path #-}

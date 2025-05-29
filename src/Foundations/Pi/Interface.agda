{-# OPTIONS --safe #-}
module Foundations.Pi.Interface where

open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Strict
open import Notation.Unitality.Inner
open import Notation.Unitality.Outer

open import Foundations.Pi.Base
  public
  renaming ( id  to idₜ
           ; _∘_ to _∘ₜ_
           )
open import Foundations.Path.Interface

Funs : Quiver-on (λ ℓ → Type ℓ) _l⊔_
Funs .Quiver-on.Hom = Fun

instance
  Fun-Refl : Reflω Funs
  Fun-Refl .refl = idₜ

  Fun-Comp : Compω Funs
  Fun-Comp .Comp._∙_ f g x = g (f x)

  Fun-Assoc : {ℓw ℓx ℓy ℓz : Level} → Assoc Funs Strict ℓw ℓx ℓy ℓz
  Fun-Assoc .Assoc.assoc _ _ _ = refl

  Fun-Unit-i : {ℓx ℓy : Level} → Unit-i Funs Strict ℓx ℓy
  Fun-Unit-i .id-i _ = refl

  Fun-Unit-o : {ℓx ℓy : Level} → Unit-o Funs Strict ℓx ℓy
  Fun-Unit-o .id-o _ = refl

{-# INCOHERENT
  Fun-Refl Fun-Comp
  Fun-Assoc Fun-Unit-i Fun-Unit-o
#-}

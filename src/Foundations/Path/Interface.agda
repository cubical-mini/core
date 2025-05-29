{-# OPTIONS --safe #-}
module Foundations.Path.Interface where

open import Prim.Kan
open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Duality
open import Notation.Reflexivity
open import Notation.Retraction
open import Notation.Retraction.Strict
open import Notation.Section
open import Notation.Section.Strict
open import Notation.Strict
open import Notation.Symmetry
open import Notation.Unitality.Inner
open import Notation.Unitality.Outer
open import Notation.Whiskering.Left
open import Notation.Whiskering.Left.Strict
open import Notation.Whiskering.Right
open import Notation.Whiskering.Right.Strict

open import Foundations.Path.Base
  public
  renaming ( refl  to reflₚ
           ; sym   to symₚ
           ; _∙_   to _∙ₚ_

           ; Square to Squareₚ
           )
open import Foundations.Path.Properties
  public
  renaming ( id-i  to id-iₚ
           ; id-o  to id-oₚ
           ; assoc to assocₚ
           ; inv-i to inv-iₚ
           ; inv-o to inv-oₚ
  )

module _ {ℓa : Level} {A : Type ℓa} where instance
  Path-Refl : {ℓ : Level} → Refl (Paths A) ℓ
  Path-Refl .refl = reflₚ

  Path-Sym : {ℓx ℓy : Level} → Symmetry (Paths A) ℓx ℓy
  Path-Sym .sym = symₚ

  Path-Comp : {ℓx ℓy ℓz : Level} → Comp (Paths A) ℓx ℓy ℓz
  Path-Comp ._∙_ = _∙ₚ_

  Path-Dual : {ℓx ℓy : Level} → Dual (Paths A) Strict ℓx ℓy
  Path-Dual .invol _ = reflₚ

  Path-Assoc : {ℓw ℓx ℓy ℓz : Level} → Assoc (Paths A) Strict ℓw ℓx ℓy ℓz
  Path-Assoc .assoc p q r = assocₚ p q r

  Path-Unit-i : {ℓx ℓy : Level} → Unit-i (Paths A) Strict ℓx ℓy
  Path-Unit-i .id-i = id-iₚ

  Path-Unit-o : {ℓx ℓy : Level} → Unit-o (Paths A) Strict ℓx ℓy
  Path-Unit-o .id-o = id-oₚ

  Path-Retraction : {ℓx ℓy : Level} {x y : A} {p : x ＝ y} → Split-mono {ℓx = ℓx} {ℓy = ℓy} p
  Path-Retraction {ℓx} {ℓy} {p} .Weak-split-mono.retraction = sym {ℓx = ℓx} {ℓy = ℓy} p
  Path-Retraction {p} .retraction-cell = inv-oₚ p

  Path-Section : {ℓx ℓy : Level} {x y : A} {p : x ＝ y} → Split-epi {ℓx = ℓx} {ℓy = ℓy} p
  Path-Section {ℓx} {ℓy} {p} .Weak-split-epi.section = sym {ℓx = ℓx} {ℓy = ℓy} p
  Path-Section {p} .section-cell = inv-iₚ p

{-# INCOHERENT
  Path-Refl Path-Sym Path-Comp
  Path-Dual Path-Assoc Path-Unit-i Path-Unit-o
  Path-Retraction Path-Section
#-}


module _ {ℓ : Level} {A : Type ℓ} where instance
  Path-Refl0 : Refl (Paths A) lzero
  Path-Refl0 = Path-Refl

  Path-Sym0 : Symmetry (Paths A) lzero lzero
  Path-Sym0 = Path-Sym

  Path-Comp0 : Comp (Paths A) lzero lzero lzero
  Path-Comp0 = Path-Comp

  Path-Dual0 : Dual (Paths A) Strict lzero lzero
  Path-Dual0 = Path-Dual

  Path-Assoc0 : Assoc (Paths A) Strict lzero lzero lzero lzero
  Path-Assoc0 = Path-Assoc

  Path-Unit-i0 : Unit-i (Paths A) Strict lzero lzero
  Path-Unit-i0 = Path-Unit-i

  Path-Unit-o0 : Unit-o (Paths A) Strict lzero lzero
  Path-Unit-o0 = Path-Unit-o

  Path-Retraction0 : {x y : A} {p : x ＝ y} → Split-mono p
  Path-Retraction0 = Path-Retraction

  Path-Section0 : {x y : A} {p : x ＝ y} → Split-epi p
  Path-Section0 = Path-Section

{-# OVERLAPPABLE
  Path-Refl0 Path-Sym0 Path-Comp0
  Path-Dual0 Path-Assoc0 Path-Unit-i0 Path-Unit-o0
  Path-Retraction0 Path-Section0
#-}

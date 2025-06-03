{-# OPTIONS --safe #-}
module Foundations.Path.Groupoid where

open import Prim.Kan
open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Duality
open import Notation.Reflexivity
open import Notation.Symmetry
open import Notation.Unitality.Inner
open import Notation.Unitality.Outer
open import Notation.Whiskering.Left
open import Notation.Whiskering.Right

open import Foundations.Idempotent
open import Foundations.Split

open import Foundations.Path.Base
  public
  renaming ( refl  to reflₚ
           ; sym   to symₚ
           ; _∙_   to _∙ₚ_

           ; Square to Squareₚ
           )
open import Foundations.Path.Groupoid.Base
  public
open import Foundations.Path.Properties
  public
  renaming ( id-i  to id-iₚ
           ; id-o  to id-oₚ
           ; assoc to assocₚ
           ; inv-i to inv-iₚ
           ; inv-o to inv-oₚ
  )
open import Foundations.Path.Groupoid.Whiskering
  public

module Path-gpd where
  module _ {ℓa} {A : Type ℓa} where instance
    Path-Refl : Reflω (Pathsω A)
    Path-Refl .refl = reflₚ

    Path-Sym : Symmetryω (Pathsω A)
    Path-Sym .sym = symₚ

    Path-Comp : Compω (Pathsω A)
    Path-Comp ._∙_ = _∙ₚ_

    Path-Dual : Dualω (Pathsω A) Strict
    Path-Dual .invol _ = reflₚ

    Path-Assoc : Assocω (Pathsω A) Strict
    Path-Assoc .assoc p q r = assocₚ p q r

    Path-Unit-i : Unit-iω (Pathsω A) Strict
    Path-Unit-i .id-i = id-iₚ

    Path-Unit-o : Unit-oω (Pathsω A) Strict
    Path-Unit-o .id-o = id-oₚ

    Path-Split : ∀{ℓx ℓy} {x y : A} {p : x ＝ y} → Split (Pathsω A) {ℓx = ℓx} {ℓy = ℓy} p (symₚ p)
    Path-Split {p} .split = inv-oₚ p

    Path-Refl-Idem : ∀{ℓ} {x : A} → Weak-Idem (Pathsω A) Strict {ℓ = ℓ} {x = x} _
    Path-Refl-Idem .idem = refl-idem

    {-# OVERLAPS
      Path-Refl Path-Sym Path-Comp
      Path-Dual Path-Assoc Path-Unit-i Path-Unit-o
      Path-Split Path-Refl-Idem
    #-}


module Path-gpd0 where
  open Path-gpd
  module _ {ℓ : Level} {A : Type ℓ} where instance
    Path-Refl0 : Refl (Pathsω A) lzero
    Path-Refl0 = Path-Refl

    Path-Sym0 : Symmetry (Pathsω A) lzero lzero
    Path-Sym0 = Path-Sym

    Path-Comp0 : Comp (Pathsω A) lzero lzero lzero
    Path-Comp0 = Path-Comp

    Path-Dual0 : Dual (Pathsω A) Strict lzero lzero
    Path-Dual0 = Path-Dual

    Path-Assoc0 : Assoc (Pathsω A) Strict lzero lzero lzero lzero
    Path-Assoc0 = Path-Assoc

    Path-Unit-i0 : Unit-i (Pathsω A) Strict lzero lzero
    Path-Unit-i0 = Path-Unit-i

    Path-Unit-o0 : Unit-o (Pathsω A) Strict lzero lzero
    Path-Unit-o0 = Path-Unit-o

    Path-Split0 : {x y : A} {p : x ＝ y} → Split (Pathsω A) {ℓx = lzero} {ℓy = lzero} p (symₚ p)
    Path-Split0 = Path-Split

    Path-Refl-Idem0 : {x : A} → Idem (Pathsω A) {ℓ = lzero} {x = x} _
    Path-Refl-Idem0 = Path-Refl-Idem

    {-# OVERLAPPABLE
      Path-Refl0 Path-Sym0 Path-Comp0
      Path-Dual0 Path-Assoc0 Path-Unit-i0 Path-Unit-o0
      Path-Split0 Path-Refl-Idem0
    #-}

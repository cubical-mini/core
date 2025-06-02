{-# OPTIONS --safe #-}
module Foundations.Path.Interface where

open import Prim.Kan
open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Duality
open import Notation.Idempotent
open import Notation.Invertibility.Retraction.Base
open import Notation.Invertibility.Section.Base
open import Notation.Reflexivity
open import Notation.Split
open import Notation.Strict
open import Notation.Symmetry
open import Notation.Unitality.Inner
open import Notation.Unitality.Outer
open import Notation.Whiskering.Left
open import Notation.Whiskering.Right

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

module Path-gpd where
  module _ {ℓa} {A : Type ℓa} where instance
    Path-Refl : Reflω (Paths A)
    Path-Refl .refl = reflₚ

    Path-Sym : Symmetryω (Paths A)
    Path-Sym .sym = symₚ

    Path-Comp : Compω (Paths A)
    Path-Comp ._∙_ = _∙ₚ_

    Path-Dual : Dualω (Paths A) Strict
    Path-Dual .invol _ = reflₚ

    Path-Assoc : Assocω (Paths A) Strict
    Path-Assoc .assoc p q r = assocₚ p q r

    Path-Unit-i : Unit-iω (Paths A) Strict
    Path-Unit-i .id-i = id-iₚ

    Path-Unit-o : Unit-oω (Paths A) Strict
    Path-Unit-o .id-o = id-oₚ

    Path-Split : ∀{ℓx ℓy} {x y : A} {p : x ＝ y} → Split-pair (Paths A) {ℓx = ℓx} {ℓy = ℓy} p (symₚ p)
    Path-Split {p} .split = inv-oₚ p

    Path-Refl-Idem : ∀{ℓ} {x : A} → Idem (Paths A) Strict {ℓ = ℓ} {x = x} _
    Path-Refl-Idem .idem = refl-idem

    {-# INCOHERENT
      Path-Refl Path-Sym Path-Comp
      Path-Dual Path-Assoc Path-Unit-i Path-Unit-o
      Path-Split Path-Refl-Idem
    #-}


module Path-gpd0 where
  open Path-gpd
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

    Path-Split0 : {x y : A} {p : x ＝ y} → Split-pair (Paths A) {ℓx = lzero} {ℓy = lzero} p (symₚ p)
    Path-Split0 = Path-Split

    Path-Refl-Idem0 : {x : A} → Idem (Paths A) Strict {ℓ = lzero} {x = x} _
    Path-Refl-Idem0 = Path-Refl-Idem

    {-# OVERLAPPABLE
      Path-Refl0 Path-Sym0 Path-Comp0
      Path-Dual0 Path-Assoc0 Path-Unit-i0 Path-Unit-o0
      Path-Split0 Path-Refl-Idem0
    #-}

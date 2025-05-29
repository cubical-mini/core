{-# OPTIONS --safe #-}
module README.Foundations.Path where

open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Foundations.Path.Base
open import Foundations.Path.Coe

magic-square : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ＝ y) (q : y ＝ z) → Square p q p q
magic-square p q j i = hcomp (∂ i ∨ ∂ j) λ where
  k (i = i0) → p j
  k (i = i1) → q (j ∧ k)
  k (j = i0) → p i
  k (j = i1) → q (i ∧ k)
  k (k = i0) → p (i ∨ j)

and-square : {ℓ : Level} {A : Type ℓ} {x y : A} (p : x ＝ y) → Square refl p refl p
and-square p j i = p (i ∧ j)

or-square : {ℓ : Level} {A : Type ℓ} {x y : A} (p : x ＝ y) → Square p refl p refl
or-square p j i = p (i ∨ j)


-- Observe the computational behaviour of `coe`!
module _ {ℓ} (A : I → Type ℓ) where
  coei0→0 : (a : A i0) → coei→0 A i0 a ＝ a
  coei0→0 _ = refl

  coei1→0 : (a : A i1) → coei→0 A i1 a ＝ coe1→0 A a
  coei1→0 _ = refl

  coei0→1 : (a : A i0) → coei→1 A i0 a ＝ coe0→1 A a
  coei0→1 _ = refl

  coei1→1 : (a : A i1) → coei→1 A i1 a ＝ a
  coei1→1 _ = refl

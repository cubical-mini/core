{-# OPTIONS --safe #-}
module Foundations.Path.Coe where

open import Prim.Interval
open import Prim.Kan
open import Prim.Type

I-eq : I → I → I
I-eq i j = (i ∧ j) ∨ (~ i ∧ ~ j)

I-interp : I → I → I → I
I-interp t x y = (~ t ∧ x) ∨ (t ∧ y) ∨ (x ∧ y)

module _ {ℓ̂ : I → Level} (A : (i : I) → Type (ℓ̂ i)) where
  coe : (i j : I) → A i → A j
  coe i j = transp (λ k → A (I-interp k i j)) (I-eq i j)

  -- forward spread
  coe0→i : (i : I) → A i0 → A i
  coe0→i i = coe i0 i -- transp (λ j → A (i ∧ j)) (~ i)

  -- backward spread
  coe1→i : (i : I) → A i1 → A i
  coe1→i i = coe i1 i -- transp (λ j → A (i ∨ ~ j)) i

  -- backward squeeze
  coei→0 : (i : I) → A i → A i0
  coei→0 i = coe i i0  -- transp (λ j → A (i ∧ ~ j)) (~ i)

  -- forward squeeze
  coei→1 : (i : I) → A i → A i1
  coei→1 i = coe i i1  -- transp (λ l → A (i ∨ l)) i

  coei→i : (i : I) (x : A i) → coe i i x ＝ x
  coei→i i x j = transp (λ _ → A i) (j ∨ ∂ i) x

  coe-path : (p : (i : I) → A i) (i j : I) → coe i j (p i) ＝ p j
  coe-path p i j k = transp
    (λ l → A (I-interp k (I-interp l i j) j))
    (I-interp k (I-eq i j) i1)
    (p (I-interp k i j))

module _ {ℓ : Level} (A : I → Type ℓ) where
  -- forward transport
  coe0→1 : A i0 → A i1
  coe0→1 = coei→1 A i0 -- transp (λ i → A i) i0

  -- backward transport
  coe1→0 : A i1 → A i0
  coe1→0 = coei→0 A i1 -- transp (λ i → A (~ i)) i0

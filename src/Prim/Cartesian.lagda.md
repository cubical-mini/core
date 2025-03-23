```agda

{-# OPTIONS --safe #-}

module Prim.Cartesian where

open import Prim.Base
  using ( Level; Type; I; i0; i1; ~_; _∨_; _∧_; transp; _≡_; funext
        ; interp-I; eq-I )
open import Prim.Pi using ( idfun )

coe : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i j : I) → A i → A j
coe A i j a = transp (λ k → A (interp-I k i j)) (eq-I i j) a

coe0→1 : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1
coe0→1 A a = transp (λ i → A i) i0 a

coe1→0 : ∀ {ℓ} (A : I → Type ℓ) → A i1 → A i0
coe1→0 A a = transp (λ i → A (~ i)) i0 a

coe0→i : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i0 → A i
coe0→i A i a = transp (λ j → A (i ∧ j)) (~ i) a

coe1→i : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i1 → A i
coe1→i A i a = transp (λ j → A (i ∨ ~ j)) i a

coei→0 : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i → A i0
coei→0 A i a = transp (λ j → A (i ∧ ~ j)) (~ i) a

coei→1 : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i → A i1
coei→1 A i a = transp (λ j → A (i ∨ j)) i a

coei→i : ∀ {ℓ} (A : I → Type ℓ) i x → coe A i i x ≡ x
coei→i A i x j = transp (λ _ → A i) (j ∨ i ∨ ~ i) x

coe-id : ∀ {ℓ} (A : I → Type ℓ) {i : I} → coe A i i ≡ idfun (A i)
coe-id A {i} = funext (coei→i A i)

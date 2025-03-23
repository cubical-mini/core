```agda

{-# OPTIONS --safe #-}

module Prim.DeMorgan where

open import Prim.Base

```

### Interpolation Proofs

Validates associativity-like behavior and boundary interactions:

```agda
module _
  {A : Type} {p : I → A} {i j k l m : I}
  where

  -- Nested interpolation preserves structure
  _ : p (interp-I i (interp-I j k l) m) ≡ p (interp-I j (interp-I i k m) (interp-I i l m))
  _ = refl

  _ : p (interp-I i j (interp-I k l m)) ≡ p (interp-I k (interp-I i j l) (interp-I i j m))
  _ = refl

  -- Boundary reductions
  _ : p (interp-I i i0 j) ≡ p (i ∧ j)
  _ = refl

  _ : p (interp-I i j i1) ≡ p (i ∨ j)
  _ = refl

  -- Negation symmetry
  _ : p (interp-I (~ i) j k) ≡ p (interp-I i k j)
  _ = refl
```

---

### Midpoint Proofs

Verifies definitional behavior and idempotence:

```agda
  _ : p (midpoint-I i j) ≡ p (interp-I (i ∧ j ∨ ~ i ∧ ~ j) i j)
  _ = refl

  -- Idempotence
  _ : p (midpoint-I i i) ≡ p i
  _ = refl
```

---

### Reflection Proofs

Demonstrates boundary behavior and negation symmetry:

```agda
  -- Boundary cases
  _ : p (reflect-I i0 i) ≡ p i
  _ = refl

  _ : p (reflect-I i1 i) ≡ p (~ i)
  _ = refl

  -- Parameter negation symmetry
  _ : p (reflect-I (~ i) j) ≡ p (reflect-I i (~ j))
  _ = refl
```

---

### Modal Proofs

Establishes boundary preservation and De Morgan duality:

```agda
  -- Boundary preservation
  _ : p (box-I i0) ≡ p i0
  _ = refl

  _ : p (diamond-I i1) ≡ p i1
  _ = refl

  -- Idempotence
  _ : p (box-I (box-I i)) ≡ p (box-I i)
  _ = refl

  _ : p (diamond-I (diamond-I i)) ≡ p (diamond-I i)
  _ = refl

  -- De Morgan duality
  _ : p (~ (box-I i)) ≡ p (diamond-I (~ i))
  _ = refl

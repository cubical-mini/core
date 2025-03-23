```agda

{-# OPTIONS --safe #-}

module Prim.Base.Interval where

open import Prim.Base.Type using ( Type; Level; _₊; _⊔_ )
open import Agda.Primitive.Cubical public
  using ( IUniv -- IUniv : SSet₁
        ; I     -- I : IUniv
        ; i0    -- i0 : I
        ; i1    -- i1 : I
        ; IsOne -- IsOne : I → Typeω
        ; Partial -- Partial : ∀{ℓ} (i : I) (A : Type ℓ) → Type ℓ
                  -- Partial i A = IsOne i → A
        ; PartialP
        ; primPOr )
  renaming ( primIMin to _∧_ -- _∧_ : I → I → I
           ; primIMax to _∨_ -- _∨_ : I → I → I
           ; primINeg to ~_  -- ~_ : I → I
           ; itIsOne    to 1=1       -- 1=1 : IsOne i1
           ; isOneEmpty to is1-empty -- is1-empty : ∀ {ℓ} {A : Partial i0 (Type ℓ)}
                                     --           → PartialP i0 A
           ; IsOne1     to is1-left  -- is1-left  : ∀ i j → IsOne i → IsOne (i ∨ j)
           ; IsOne2     to is1-right -- is1-right : ∀ i j → IsOne j → IsOne (i ∨ j)
           ; primTransp to transp
           )

```

Note from Cubical.Core.Primitives (commit cd8c842):

> These two are to make sure all the primitives are loaded and ready
> to compute hcomp/transp for the universe.

See (agda/cubical #250)[https://github.com/agda/cubical/issues/250]
for discussion.

So we include the HCompU module, which is commented out there, because
they only say they did not include this import due to older versions
of Agda not having it.

```

import Agda.Builtin.Cubical.Glue
import Agda.Builtin.Cubical.HCompU

```

We import the basic Path primitives here

```

open import Agda.Builtin.Cubical.Path public
  renaming ( _≡_ to infix 2 _≡_ )

infix 4 _[_≡_]

_[_≡_] : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1 → Type ℓ
_[_≡_] = PathP

Path : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
Path A = PathP (λ _ → A)

```

We open the following trivial helpers here

> module _ {ℓ} {A : Type ℓ} where
>   refl : {x : A} → x ≡ x
>   refl {x = x} = λ _ → x
>
>   sym : {x y : A} → x ≡ y → y ≡ x
>   sym p = λ i → p (~ i)
>
>   cong : ∀ {ℓ'} {B : A → Type ℓ'} {x y : A}
>          (f : (a : A) → B a) (p : x ≡ y)
>        → PathP (λ i → B (p i)) (f x) (f y)
>   cong f p = λ i → f (p i)

```

open Agda.Builtin.Cubical.HCompU.Helpers public
  using ( refl; sym )
  renaming ( cong to ap ) -- We use standard HoTT terminology for `cong`

iℓ : Type
iℓ = I → Level

IType : (ℓ : iℓ) (i : I) → Type (ℓ i ₊)
IType ℓ i = Type (ℓ i)

funext : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x}
       → ((x : A) → f x ≡ g x) → f ≡ g
funext p i x = p x i

∂ : I → I
∂ i = i ∨ ~ i

eq-I : I → I → I
eq-I i j = (i ∧ j) ∨ (~ i ∧ ~ j)

```

Blends between two interval values while respecting boundaries and overlaps

```

interp-I : I → I → I → I
interp-I t i j = (~ t ∧ i) ∨ (t ∧ j) ∨ (i ∧ j)
```

**Behavior**:
- At `t = i0`: `(~i0 ∧ i) ∨ ... ≡ i ∨ ...` (favors left input)
- At `t = i1`: `... ∨ (i1 ∧ j) ≡ ... ∨ j` (favors right input)
- Term `(i ∧ j)` preserves overlapping regions

---

Computes a symmetric midpoint using De Morgan duality:

```agda
midpoint-I : I → I → I
midpoint-I i j = interp-I (i ∧ j ∨ ~ i ∧ ~ j) i j
```
- Control parameter `(i ∧ j) ∨ (~i ∧ ~j)` balances:
  - Overlap regions (`i ∧ j`)
  - Mutual exclusion (`~i ∧ ~j`)

---

Constructs paths between values and their negations:

```agda
reflect-I : I → I → I
reflect-I p i = interp-I i p (~ p)
```

**Behavior**:
- `reflect-I i0 i = i` (identity)
- `reflect-I i1 i = ~i` (full negation)

---

### Modal Operators

Encode necessity (□) and possibility (◇) from modal logic:

```agda
box-I : I → I  -- Necessity
box-I i = i ∧ (i ∨ ~ i)

diamond-I : I → I  -- Possibility
diamond-I i = i ∨ (i ∧ ~ i)
```

**Duality**:
`¬□i ≡ ◇¬i` (Negating necessity yields possibility of negation)

---

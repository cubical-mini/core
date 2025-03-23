```agda

{-# OPTIONS --safe #-}

module Lib.Path.test where

open import Prim.Base
open import Prim.Kan
open import Prim.DeMorgan
open import Prim.Data.Sigma

```

Recall the following definitions, exposed in Prim.Base.Builtin:

> refl : {x : A} → x ≡ x
> refl {x = x} = λ _ → x

> sym : {x y : A} → x ≡ y → y ≡ x
> sym p = λ i → p (~ i)

> -- Action on paths. Renamed from `cong` to keep with traditional
> -- HoTT notation as opposed to agda-stdlib convention.
> ap : ∀ {ℓ'} {B : A → Set ℓ'} {x y : A}
>        (f : (a : A) → B a) (p : x ≡ y)
>      → PathP (λ i → B (p i)) (f x) (f y)
> ap f p = λ i → f (p i)

# Path Induction and Transport

First we'll define J


Most Cubical formalizations use the name `transport` to denote a
function we will instead define in the module for Equivalence
(i.e. their `transport` will be our `pathtofun`).

Here we reserve the notion of transport for the usual notion in HoTT
literature. We will follow Rijke's shortened notation for this
operator, against the usual name `subst` given in most Cubical
developments (departing from agda-stdlib convention).

```

tr : ∀ {ℓ ℓ'} {A : Type ℓ} (P : A → Type ℓ') → ∀ {x y} → x ≡ y → P x → P y
tr P {x} q = transp (λ i → P (q i)) i0

```

For the following definitions fix a type in an anonymous module

```

module _ {ℓ} {A : Type ℓ} where

```

First we'll define path composition, beginning with double composition,
"the most natural notion of homogenous double composition" as noted by
Cubical.Foundations.Prelude. Quoting from their module, our goal is to
connect the top portion of the diagram.


>      w ∙ ∙ ∙ > z
>      ^         ^
>  p⁻¹ |         | r        ^
>      |         |        j |
>      x — — — > y          ∙ — >
>           q                 i
>
>  `p ∙∙ q ∙∙ r` gives the line at the top,
>  `doubleCompPath-filler p q r` gives the whole square

```
  module _ {w x y z : A} where
    _∙∙_∙∙_ : w ≡ x → x ≡ y → y ≡ z → w ≡ z
    (p ∙∙ q ∙∙ r) i = hcomp (∂ i) faces
      module comp₂-path where
        faces : (j : I) → Partial (∂ i ∨ ~ j) A
        faces j (i = i0) = p (~ j)
        faces j (i = i1) = r j
        faces j (j = i0) = q i

  -- single path composition arises as a particular case
  _∙_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  p ∙ q = refl ∙∙ p ∙∙ q

```

The square type is a useful representation

```
  Square : {a00 a01 a10 a11 : A}
         → (p : a00 ≡ a01) (q : a00 ≡ a10) (s : a01 ≡ a11) (r : a10 ≡ a11)
         → Type ℓ
  Square p q s r = PathP (λ i → p i ≡ r i) q s


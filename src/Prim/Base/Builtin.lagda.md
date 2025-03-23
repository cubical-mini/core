This is a module that basically holds all of the Agda builtin-specific
machinery including the machinery needed for the notion of equivalence
favored by Agda's Cubical type theory necessary to implement
univalence.

Read the Cubical section of the Agda manual for reference:
https://agda.readthedocs.io/en/latest/language/cubical.html

```agda

{-# OPTIONS --safe #-}

module Prim.Base.Builtin where

import Agda.Builtin.Cubical.HCompU
import Agda.Builtin.Cubical.Glue

```

Following TypeTopology, we will call the builtin notion of equivalence
"fiberwise equivalences"

```

open import Agda.Builtin.Cubical.Equiv public
  using ()
  renaming ( _≃_           to infix 1 _≃ᶠ_
           ; isEquiv       to is-fiberwise-equiv
           ; equiv-proof   to fibeqv-witness
           ; equivFun      to feqv-fun
           ; equivProof    to feqv-proof
           ; pathToisEquiv to path→is-fiberwise-equiv
           ; pathToEquiv   to path→FEqv )

```

Let's aggregate all the core primitives and pragmas under the
following "Prim" module for convenience, available to the whole
library. Cubical Builtin-specific names ought to never be opened so
that whenever they appear in the main lib we may easily distinguish
them

For a list of the all the functions opened in Helpers in the Prim
submodule, refer to below:

>  -- Homogeneous filling
>  hfill : ∀ {ℓ} {A : Type ℓ} {φ : I}
>            (u : ∀ i → Partial φ A)
>            (u0 : A [ φ ↦ u i0 ]) (i : I) → A
>  hfill {φ = φ} u u0 i =
>    hcomp (λ j → \ { (φ = i1) → u (i ∧ j) 1=1
>                   ; (i = i0) → outS u0 })
>          (outS u0)

>  -- Heterogeneous filling defined using comp
>  fill : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) {φ : I}
>           (u : ∀ i → Partial φ (A i))
>           (u0 : A i0 [ φ ↦ u i0 ]) →
>           ∀ i →  A i
>  fill A {φ = φ} u u0 i =
>    comp (λ j → A (i ∧ j))
>         (λ j → \ { (φ = i1) → u (i ∧ j) 1=1
>                  ; (i = i0) → outS u0 })
>         (outS {φ = φ} u0)

And because it is part of the definition of fiberwise equivalences,
we will have access to the Builtin version of is-contr through the
Prim helper module:

> isContr : ∀ {ℓ} → Type ℓ → Type ℓ
> isContr A = Σ A \ x → (∀ y → x ≡ y)

```

private module H = Agda.Builtin.Cubical.HCompU.Helpers

module Prim where
  open import Agda.Primitive.Cubical public
    using ( primComp; primHComp )

  open Agda.Builtin.Cubical.Glue public
    using ( primGlue; prim^glue; prim^unglue )

  -- primFaceForall is not used, Helpers we want to import
  -- here directly, so we hide it in this submodule
  open Agda.Builtin.Cubical.HCompU public
    hiding ( primFaceForall; module Helpers )

  open H public
    using ( isContr; fill; hfill ) public

```

Because the fiber type is theoretically fundamental, and our chosen
definition does not deviate from it we introduce this builtin
to the top-level namespace

> fiber : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ ⊔ ℓ')
> fiber {A = A} f y = Σ A \ x → f x ≡ y

```
open H using ( fiber ) public
{-# INLINE fiber #-}

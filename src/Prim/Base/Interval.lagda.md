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

open import Agda.Builtin.Cubical.Path public
  renaming ( _≡_ to infix 2 _＝_ )

iℓ : Type
iℓ = I → Level

IType : (ℓ : iℓ) (i : I) → Type (ℓ i ₊)
IType ℓ i = Type (ℓ i)

∂ : I → I
∂ i = ~ i ∨ i

eq-I : I → I → I
eq-I i j = (i ∧ j) ∨ (~ i ∧ ~ j)

interp-I : I → I → I → I
interp-I t i j = (~ t ∧ i) ∨ (t ∧ j) ∨ (i ∧ j)

midpoint-I : I → I → I
midpoint-I i j = interp-I (i ∧ j ∨ ~ i ∧ ~ j) i j

```

Inspired by necessity (square) and possibility (diamond) from modal logic.

Negating necessity yields possibility of negation:

>  `~ (□ i) ＝ ◇ (~ i)`

```agda
box-I : I → I  -- Necessity
box-I i = i ∧ (i ∨ ~ i)

dia-I : I → I  -- Possibility
dia-I i = i ∨ (i ∧ ~ i)

```

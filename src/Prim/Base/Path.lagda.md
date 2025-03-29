We import the basic Path primitives here, and define basic operations for paths

```agda

{-# OPTIONS --safe #-}

module Prim.Base.Path where

open import Prim.Base.Type
open import Prim.Base.Interval
open import Prim.Base.Kan using ( hcomp )

import Agda.Builtin.Cubical.HCompU

infix 4 _[_＝_]
infixr 30 _∙_

_[_＝_] : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1 → Type ℓ
_[_＝_] = PathP

Path : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
Path A = PathP (λ _ → A)

erefl : ∀ {ℓ} {A : Type ℓ} (x : A) → x ＝ x
erefl x i = x

syntax erefl x = x ∎

```

We open the following trivial helpers here

> module _ {ℓ} {A : Type ℓ} where
>   refl : {x : A} → x ＝ x
>   refl {x = x} = λ _ → x
>
>   sym : {x y : A} → x ＝ y → y ＝ x
>   sym p = λ i → p (~ i)
>
>   cong : ∀ {ℓ'} {B : A → Type ℓ'} {x y : A}
>          (f : (a : A) → B a) (p : x ＝ y)
>        → PathP (λ i → B (p i)) (f x) (f y)
>   cong f p = λ i → f (p i)

```
private module H = Agda.Builtin.Cubical.HCompU.Helpers
open H public
  using ( refl; sym )
  renaming ( cong to ap ) -- We use standard HoTT terminology for `cong`

```

This will be identical to the definition of double composition we have
later. Still, we define it here because we'd like to have all of the
groupoid operations for paths early as possible.

```

_∙_ : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
_∙_ {x = x} p q i = hcomp (∂ i) λ where
  j (i = i0) → x
  j (i = i1) → q j
  j (j = i0) → p i

```

Finally, given the fundamental relevance of this definition in
univalent type theory we export `funext` here, as well as its
inverse opperation `happly`.

```

funext : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x}
       → ((x : A) → f x ＝ g x) → f ＝ g
funext p i x = p x i

-- happly is an on-the-nose inverse to funext
happly : ∀ {a b} {A : Type a} {B : A → Type b} {f g : (x : A) → B x}
       → f ＝ g → (x : A) → f x ＝ g x
happly p x i = p i x

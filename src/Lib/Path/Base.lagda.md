```agda

{-# OPTIONS --safe #-}

module Lib.Path.Base where

open import Prim.Base
open import Prim.Pi
open import Prim.Data.Sigma

```

Recall the following definitions, exposed in Prim.Base.Builtin:

> refl : {x : A} → x ＝ x
> refl {x = x} = λ _ → x

> sym : {x y : A} → x ＝ y → y ＝ x
> sym p = λ i → p (~ i)

We'll define the PathP version of sym:

```

symP : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1}
     → PathP A x y → PathP (λ i → A (~ i)) y x
symP p i = p (~ i)

```

The square type is a useful type definition so we will define it here along with
its PathP variant. Thanks to 1lab once again.

```

Square : ∀ {ℓ} {A : Type ℓ}
       → {a₀₀ a₀₁ : A} (p : a₀₀ ＝ a₀₁)
       → {a₁₀ : A} (q : a₀₀ ＝ a₁₀)
       → {a₁₁ : A} (r : a₁₀ ＝ a₁₁) (s : a₀₁ ＝ a₁₁)
       → Type ℓ
Square p q r s = PathP (λ i → p i ＝ r i) q s
syntax Square p q r s = p >> s ≈ q >> r

SquareP : ∀ {ℓ} (A : I → I → Type ℓ)
        → {a₀₀ : A i0 i0} {a₀₁ : A i0 i1}
        → {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
        → (p : PathP (λ i → A i i0) a₀₀ a₁₀)
        → (q : PathP (λ j → A i0 j) a₀₀ a₀₁)
        → (s : PathP (λ j → A i1 j) a₁₀ a₁₁)
        → (r : PathP (λ i → A i i1) a₀₁ a₁₁)
        → Type ℓ
SquareP A p q s r = PathP (λ i → PathP (λ j → A i j) (p i) (r i)) q s

module _ {ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
  {p : a00 ＝ a01} {q : a00 ＝ a10} {r : a10 ＝ a11} {s : a01 ＝ a11}
  where
  hflip : Square p q r s → Square (sym p) s (sym r) q
  hflip α i j = α (~ i) j

  vflip : Square p q r s → Square r (sym q) p (sym s)
  vflip α i j = α i (~ j)

  lrotate : Square p q r s → Square s (sym p) q (sym r)
  lrotate α i j = α (~ j) i

  rrotate : Square p q r s → Square (sym q) r (sym s) p
  rrotate α i j = α j (~ i)

  transpose : Square p q r s → Square q p s r
  transpose α i j = α j i

```

> -- Action on paths. Renamed from `cong` to keep with traditional
> -- HoTT notation as opposed to agda-stdlib convention.
> ap : ∀ {ℓ'} {B : A → Set ℓ'} {x y : A}
>        (f : (a : A) → B a) (p : x ＝ y)
>      → PathP (λ i → B (p i)) (f x) (f y)
> ap f p = λ i → f (p i)

We'll define the non-dependent, interval-indexed, and binary versions
here as well. Further variants will be in other modules.

(TODO: Reference said "other modules" here)

```
module _ {ℓ ℓ'} where
  aps : {A : Type ℓ} {B : Type ℓ'} {x y : A} (f : A → B) → x ＝ y → f x ＝ f y
  aps f p i = f (p i)
  {-# INLINE aps #-}

  apd : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
      → (f : (i : I) → (a : A i) → B i a) {x : A i0} {y : A i1}
      → (p : PathP A x y) → PathP (λ i → B i (p i)) (f i0 x) (f i1 y)
  apd f p i = f i (p i)
  {-# INLINE apd #-}

module _ {u v w} {A : Type u} where
  ap2 : {B : A → Type v} {C : (s : A) → B s → Type w}
      → (f : (s : A) (t : B s) → C s t) {x y : A} {a : B x} {b : B y}
      → (p : x ＝ y) (q : PathP (λ i → B (p i)) a b)
      → PathP (λ i → C (p i) (q i)) (f x a) (f y b)
  ap2 f p q i = f (p i) (q i)
  {-# INLINE ap2 #-}

  ap2s : {B : Type v} {C : A → B → Type w}
       → (f : (s : A) (t : B) → C s t) {x y : A} {a b : B}
       → (p : x ＝ y) (q : a ＝ b) → PathP (λ i → C (p i) (q i)) (f x a) (f y b)
  ap2s f p q i = f (p i) (q i)
  {-# INLINE ap2s #-}

```

Most Cubical formalizations use the name `transport` to denote what is usually
called idtofun. We'll have both notations.

```

transport : ∀ {ℓ} {A B : Type ℓ} → A ＝ B → A → B
transport p a = transp (λ i → p i) i0 a

```

Against the usual name `subst` given in most Cubical developments, we
will follow Rijke's shortened notation for this operator (departing
from agda-stdlib convention). And we'll also define the 2-dimensional
variant.

```

tr : ∀ {ℓ ℓ'} {A : Type ℓ} (P : A → Type ℓ')
   → {x y : A} → x ＝ y → P x → P y
tr P {x} q = transp (λ i → P (q i)) i0

tr2 : ∀ {u v w} {A : Type u} {B : A → Type v}
    → (P : (x : A) → B x → Type w)
    → {a a' : A} {b : B a} {b' : B a'}
    → (p : a ＝ a') (q : PathP (λ i → B (p i)) b b') → P a b → P a' b'
tr2 P p q = transp (λ i → P (p i) (q i)) i0

```

Recall the canonical definition of fiber

> fiber : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ ⊔ ℓ')
> fiber {A = A} f y = Σ x ∶ A , f x ＝ y

We'll define the Singleton type as the canonical fiber on the identity map,
then show this fiber is contractible.

```

Singl : ∀ {ℓ} {A : Type ℓ} → A → Type ℓ
Singl {A = A} a = Σ x ∶ A , a ＝ x 

Singl-contr : ∀ {ℓ} {A : Type ℓ}
            → {x : A} (y : Singl x) → (x , refl) ＝ y
Singl-contr (y , p) = λ i → p i , λ j → p (i ∧ j)

```

Now we have what we need to define Path induction, otherwise known as J.

```

J : ∀ {ℓ ℓ'} {A : Type ℓ} {x : A} (P : (y : A) → x ＝ y → Type ℓ')
  → P x refl → ∀ {y} (p : x ＝ y) → P y p
J {x = x} P b {y} p = tr2 P p coh b where
  contr : (x , refl) ＝ (y , p)
  contr = Singl-contr (y , p)

  coh : PathP (λ i → x ＝ ap fst contr i) refl p
  coh i j = p (i ∧ j)

J>_ : ∀ {ℓ ℓ'} {A : Type ℓ} {x : A} {P : (y : A) → x ＝ y → Type ℓ'}
    → P x refl → ∀ y → (p : x ＝ y) → P y p
J>_ {P = P} r _ p = J P r p 

```

1lab had a very good idea, which they relegate to a mere demonstration,
but which may actually be good notation to consider.

```
-- canonical-path : ∀ {ℓ} (A : I → Type ℓ) → A i0 ＝ A i1
-- canonical-path A i = A i

-- canonical-filler : ∀ {ℓ} (A : I → I → Type ℓ) → PathP (λ j → I → Type ℓ) (A i0) (A i1)
-- canonical-filler A i j = A i j

-- reflP : ∀ {ℓ} {A : I → Type ℓ} {x : (i : I) → A i} → PathP A (x i0) (x i1)
-- reflP {x = x} i = x i

-- H : ∀ {ℓ ℓ'} {A : I → I → Type ℓ} {i : I} {x : ∀ i → A i i0}
--   → (C : {j : I} (y : A j i0) → PathP (λ k → A k j) ? {!!} → Type ℓ')
--   → (y : ∀ i → A i i1) (h : (i : I) → PathP (A i) (x i) (y i))
--   → C (x i) reflP → C {!!} (h i)
-- H {A = A} {x} C y h = {!!}

-- J' : ∀ {ℓ ℓ'} {A : Type ℓ} {x : A} (P : (y : A) → x ＝ y → Type ℓ')
--    → P x refl → ∀ {y} (p : x ＝ y) → P y p
-- J' {x = x} P b {y} p = H (λ y p → P {!!} p) (λ _ → {!x!}) (λ _ → {!!}) {!!}
```

Finally, although we already defined path composition, we will also
construct double composition, "the most natural notion of homogenous
double composition" as noted by Cubical.Foundations.Prelude.  Quoting
from their module, our goal is to connect the top portion of the
diagram:


>      w ∙ ∙ ∙ > z
>      ^         ^
>  p⁻¹ |         | r        ^
>      |         |        j |
>      x — — — > y          ∙ — >
>           q                 i
>
>  `p ∙∙ q ∙∙ r` gives the line at the top,

```

_∙∙_∙∙_ : ∀ {ℓ} {A : Type ℓ} {w x y z : A} → w ＝ x → x ＝ y → y ＝ z → w ＝ z
(p ∙∙ q ∙∙ r) i = hcomp (∂ i) λ where
  j (i = i0) → p (~ j)
  j (i = i1) → r j
  j (j = i0) → q i

```

Note: when we defined path composition in Prim.Base.Path, the
definition was crafted so it exactly coincides with the definition
above, see below,

```

private module _ {ℓ} {A : Type ℓ} {x y z : A} where
  _ : _∙∙_∙∙_ {A = A} {w = x} refl ＝ _∙_ {A = A} {x} {y} {z}
  _ = refl

```

Of course we need to have standard path reasoning syntax

```

path-reasoning-syntax : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A}
                      → x ＝ y → y ＝ z → x ＝ z
path-reasoning-syntax x {y} {z} p q = _∙_ {x = x} {y} {z} p q

syntax path-reasoning-syntax x p q = x ＝⟨ p ⟩ q

```

Another interesting pattern is modulating an equality over a higher path.
Consider a PathP like the following, for a path `p q : x ＝ y`.

> `PathP (λ i → refl {x} ＝ refl {y}) p q`

Here we see that the equality between p and q will be modulated over the
deformation of the reflexivity path to the reflexivity path of y. To generalize
from this pattern, we can make the following type:

```

path-mod-syntax : ∀ {u v} {A : Type u} {x y : A}
                → (p : x ＝ y)  {B : A → Type v}
                → {a : B (p i0)} {b : B (p i1)}
                → PathP (λ i → B (p i)) a b
                → PathP (λ i → B (p i)) a b
                → Type v
path-mod-syntax p {B} {a} {b} r s = PathP (λ i → PathP (λ i → B (p i)) a b) r s

syntax path-mod-syntax p a b = a ＝ b ／ p
{-# DISPLAY path-mod-syntax _ r s = r ＝ s #-}

```

Recall Idiom

```

record Recall {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  (f : (x : A) → B x) (x : A) (y : B x) : Type (ℓ ⊔ ℓ') where
  constructor ⟪_⟫
  field eq : f x ＝ y

recall : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
         (f : (x : A) → B x) (x : A)
       → Recall f x (f x)
recall _ _ = ⟪ refl ⟫

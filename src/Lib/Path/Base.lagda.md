```agda

{-# OPTIONS --safe #-}

module Lib.Path.Base where

open import Prim.Base
open import Prim.Pi
open import Prim.Kan
open import Prim.Data.Sigma

```

Recall the following definitions, exposed in Prim.Base.Builtin:

> refl : {x : A} → x ≡ x
> refl {x = x} = λ _ → x

> sym : {x y : A} → x ≡ y → y ≡ x
> sym p = λ i → p (~ i)

The square type is a useful type definition so we will define it here along with
its PathP variant

```
Square : ∀ {ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
       → (p : a00 ≡ a01) (q : a00 ≡ a10) (s : a01 ≡ a11) (r : a10 ≡ a11)
       → Type ℓ
Square p q s r = PathP (λ i → p i ≡ r i) q s

SquareP : ∀ {ℓ} (A : I → I → Type ℓ)
        → {a₀₀ : A i0 i0} {a₀₁ : A i0 i1}
        → {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
        → (p : PathP (λ i → A i i0) a₀₀ a₁₀)
        → (q : PathP (λ j → A i0 j) a₀₀ a₀₁)
        → (s : PathP (λ j → A i1 j) a₁₀ a₁₁)
        → (r : PathP (λ i → A i i1) a₀₁ a₁₁)
        → Type ℓ
SquareP A p q s r = PathP (λ i → PathP (λ j → A i j) (p i) (r i)) q s

```

> -- Action on paths. Renamed from `cong` to keep with traditional
> -- HoTT notation as opposed to agda-stdlib convention.
> ap : ∀ {ℓ'} {B : A → Set ℓ'} {x y : A}
>        (f : (a : A) → B a) (p : x ≡ y)
>      → PathP (λ i → B (p i)) (f x) (f y)
> ap f p = λ i → f (p i)

We'll define the non-dependent, interval-indexed, and binary versions
here as well. Further variants will be in other modules.

(TODO: Reference said "other modules" here)

```
module _ {ℓ ℓ'} where
  aps : {A : Type ℓ} {B : Type ℓ'} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
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
      → (p : x ≡ y) (q : PathP (λ i → B (p i)) a b)
      → PathP (λ i → C (p i) (q i)) (f x a) (f y b)
  ap2 f p q i = f (p i) (q i)
  {-# INLINE ap2 #-}

  ap2s : {B : Type v} {C : A → B → Type w}
       → (f : (s : A) (t : B) → C s t) {x y : A} {a b : B}
       → (p : x ≡ y) (q : a ≡ b) → PathP (λ i → C (p i) (q i)) (f x a) (f y b)
  ap2s f p q i = f (p i) (q i)
  {-# INLINE ap2s #-}

```

Most Cubical formalizations use the name `transport` to denote a
function we will instead define in the module for Equivalence
(i.e. their `transport` will be our `idtofun`). Let's define it below.

```

idtofun : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A → B
idtofun p a = transp (λ i → p i) i0 a

```

Here we reserve the notion of transport for the usual notion in HoTT
literature. We will follow Rijke's shortened notation for this
operator, against the usual name `subst` given in most Cubical
developments (departing from agda-stdlib convention). And we'll also
define the other variant.

```

tr : ∀ {ℓ ℓ'} {A : Type ℓ} (P : A → Type ℓ') → ∀ {x y} → x ≡ y → P x → P y
tr P {x} q = transp (λ i → P (q i)) i0

tr2 : ∀ {u v w} {A : Type u} {B : A → Type v} (P : (x : A) → B x → Type w)
    → {a a' : A} {b : B a} {b' : B a'}
    → (p : a ≡ a') (q : PathP (λ i → B (p i)) b b') → P a b → P a' b'
tr2 P p q = transp (λ i → P (p i) (q i)) i0

```

Recall the canonical definition of fiber

> fiber : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ ⊔ ℓ')
> fiber {A = A} f y = Σ x ∶ A , f x ≡ y

We'll define the Singleton type as the canonical fiber on the identity map,
then show this fiber is contractible.

```

Singl : ∀ {ℓ} {A : Type ℓ} → A → Type ℓ
Singl = fiber id

Singl-contr : ∀ {ℓ} {A : Type ℓ} → {x : A} (y : Singl x) → (x , refl) ≡ y
Singl-contr (y , p) = λ i → p (~ i) , λ j → p (~ i ∨ j)

```

Now we have what we need to define Path induction, otherwise known as J.

```

J : ∀ {ℓ ℓ'} {A : Type ℓ} {x : A} (P : (y : A) → x ≡ y → Type ℓ')
  → P x refl → ∀ {y} (p : x ≡ y) → P y p
J {x = x} P b {y} p = tr2 P p coh b where
  contr : (x , refl) ≡ (y , sym p)
  contr = Singl-contr (y , sym p)

  coh : PathP (λ i → x ≡ ap (λ r → fst r) contr i) refl p
  coh i j = p (i ∧ j)

```

Finally we'll define path composition, beginning with double composition,
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

```

_∙∙_∙∙_ : ∀ {ℓ} {A : Type ℓ} {w x y z : A} → w ≡ x → x ≡ y → y ≡ z → w ≡ z
(p ∙∙ q ∙∙ r) i = hcomp (∂ i) faces
  module dblcomp-path where
    faces : (j : I) → Partial (∂ i ∨ ~ j) _
    faces j (i = i0) = p (~ j)
    faces j (i = i1) = r j
    faces j (j = i0) = q i

-- single path composition is defined in terms of double composition
_∙_ : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = refl ∙∙ p ∙∙ q

```

Recall Idiom


```

record Recall {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  (f : (x : A) → B x) (x : A) (y : B x) : Type (ℓ ⊔ ℓ') where
  constructor ⟪_⟫
  field eq : f x ≡ y

recall : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
         (f : (x : A) → B x) (x : A)
       → Recall f x (f x)
recall _ _ = ⟪ refl ⟫

{-# OPTIONS --safe #-}
module Foundations.Path.Base where

open import Prim.Data.Sigma
open import Prim.Interval
open import Prim.Kan
open import Prim.Type

-- Path space of dependent functions

ap : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
     (f : (a : A) → B a)
     {x y : A} (p : x ＝ y)
   → Pathᴾ (λ i → B (p i)) (f x) (f y)
ap f p i = f (p i)

ap² : ∀{ℓa ℓb ℓc} {A : Type ℓa} {B : A → Type ℓb} {C : (a : A) (b : B a) → Type ℓc}
      (f : (a : A) (b : B a) → C a b)
      {x y : A} (p : x ＝ y)
      {u : B x} {v : B y} (q : Pathᴾ (λ i → B (p i)) u v)
    → Pathᴾ (λ i → C (p i) (q i)) (f x u) (f y v)
ap² f p q i = f (p i) (q i)

apᴾ : ∀{ℓa ℓb} {A : I → Type ℓa} {B : (i : I) → A i → Type ℓb}
      (f : (i : I) (a : A i) → B i a)
      {x : A i0} {y : A i1} (p : Pathᴾ A x y)
    → Pathᴾ (λ i → B i (p i)) (f i0 x) (f i1 y)
apᴾ f p i = f i (p i)


fun-ext : ∀{ℓa ℓb} {A : Type ℓa} {B : A → I → Type ℓb}
          {f : (a : A) → B a i0} {g : (a : A) → B a i1}
        → ((a : A) → Pathᴾ (B a) (f a) (g a))
        → Pathᴾ (λ i → (x : A) → B x i) f g
fun-ext p i x = p x i

happly : ∀{ℓa ℓb} {A : Type ℓa} {B : A → I → Type ℓb}
         {f : (a : A) → B a i0} {g : (a : A) → B a i1}
       → Pathᴾ (λ i → (a : A) → B a i) f g
       → (x : A) → Pathᴾ (B x) (f x) (g x)
happly eq x i = eq i x


-- Path space of dependent pairs

Σ-pathᴾ
  : ∀{ℓa ℓb} {A : I → Type ℓa} {B : ∀ i → A i → Type ℓb}
    {x : Σ (A i0) (B i0)} {y : Σ (A i1) (B i1)}
    (p : Pathᴾ A (x .fst) (y .fst))
    (q : Pathᴾ (λ i → B i (p i)) (x .snd) (y .snd))
  → Pathᴾ (λ i → Σ (A i) (B i)) x y
Σ-pathᴾ p q i = p i , q i

_,ₚ_ = Σ-pathᴾ
infixr 40 _,ₚ_


-- Basic results about paths

Square : ∀{ℓ} {A : Type ℓ}
         {w x : A} (p : w ＝ x)
         {y z : A} (r : y ＝ z)
         (q : w ＝ y) (s : x ＝ z)
       → Type ℓ
Square p r q s = Pathᴾ (λ i → p i ＝ r i) q s

Squareᴾ
  : ∀{ℓ} (A : I → I → Type ℓ)
    {w : A i0 i0} {x : A i0 i1} (p : Pathᴾ (λ j → A i0 j) w x)
    {y : A i1 i0} {z : A i1 i1} (r : Pathᴾ (λ j → A i1 j) y z)
    (q : Pathᴾ (λ i → A i i0) w y) (s : Pathᴾ (λ i → A i i1) x z)
  → Type ℓ
Squareᴾ A p r q s = Pathᴾ (λ i → Pathᴾ (λ j → A j i) (p i) (r i)) q s

refl : ∀{ℓ} {A : Type ℓ} {x : A} → x ＝ x
refl {x} _ = x

sym : ∀{ℓ} {A : Type ℓ} {x y : A} → x ＝ y → y ＝ x
sym p i = p (~ i)

-- double whiskering
infix 280 _∙∙_∙∙_
_∙∙_∙∙_ : ∀{ℓ} {A : I → Type ℓ}
          {w x : A i0} (p : x ＝ w) {y z : A i1} (q : Pathᴾ A w y) (r : y ＝ z)
        → Pathᴾ A x z
(p ∙∙ q ∙∙ r) i = hcomp (∂ i) sys
  module ∙∙-sys where
  sys : ∀ j → Partial (∂ i ∨ ~ j) _
  sys j (i = i0) = p (~ j)
  sys j (i = i1) = r j
  sys j (j = i0) = q i
{-# DISPLAY hcomp _ (∙∙-sys.sys {ℓ} {A} {w} {x} p {y} {z} q r i) = _∙∙_∙∙_ {ℓ} {A} {w} {x} p {y} {z} q r i #-}

opaque
  ∙∙-filler : ∀{ℓ} {A : I → Type ℓ}
              {w x : A i0} (p : x ＝ w) {y z : A i1} (q : Pathᴾ A w y) (r : y ＝ z)
            → Squareᴾ (λ i _ → A i) (sym p) r q (p ∙∙ q ∙∙ r)
  ∙∙-filler p q r k i = hfill (∂ i) k (∙∙-sys.sys p q r i)

opaque
  ∙∙-unique : ∀{ℓ} {A : Type ℓ}
              {w x : A} (p : x ＝ w) {y z : A} (r : y ＝ z) (q : w ＝ y)
              (α β : Σ (x ＝ z) λ s → Square (sym p) r q s)
            → α ＝ β
  ∙∙-unique {w} {x} p {y} {z} r q (α , α-fill) (β , β-fill) i = cube i i1 , λ j → cube i j where
    cube : (i j : I) → p (~ j) ＝ r j
    cube i j k = hfill (∂ i ∨ ∂ k) j λ where
      j (i = i0) → α-fill j k
      j (i = i1) → β-fill j k
      j (k = i0) → p (~ j)
      j (k = i1) → r j
      j (j = i0) → q k


∙∙-contract : ∀{ℓ} {A : Type ℓ}
              {w x : A} (p : x ＝ w) {y z : A} (r : y ＝ z) (q : w ＝ y)
              (β : Σ (x ＝ z) λ s → Square (sym p) r q s)
            → (p ∙∙ q ∙∙ r , ∙∙-filler p q r) ＝ β
∙∙-contract p r q = ∙∙-unique p r q (p ∙∙ q ∙∙ r , ∙∙-filler p q r)


-- For single homogenous path composition, we take `refl` as the top side:
opaque
  infixl 290 _∙_
  _∙_ : ∀{ℓ} {A : Type ℓ} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
  p ∙ q = p ∙∙ refl ∙∙ q

  ∙-filler-l : ∀{ℓ} {A : Type ℓ} {x y z : A} (p : x ＝ y) (q : y ＝ z)
             → Square refl q p (p ∙ q)
  ∙-filler-l {A} {y} p q i j = hcomp (~ i ∨ ∂ j) sys
    module ∙-filler-l-sys where
    sys : (k : I) → Partial (~ i ∨ ∂ j ∨ ~ k) A
    sys k (i = i0) = p (j ∨ ~ k)
    sys k (j = i0) = p (~ k)
    sys k (j = i1) = q (i ∧ k)
    sys k (k = i0) = y
  {-# DISPLAY hcomp _ (∙-filler-l-sys.sys {ℓ} {A} {x} {y} {z} p q i j) = ∙-filler-l {ℓ} {A} {x} {y} {z} p q i j #-}

  ∙-filler : ∀{ℓ} {A : Type ℓ} {x y z : A} (p : x ＝ y) (q : y ＝ z)
           → Square (sym p) q refl (p ∙ q)
  ∙-filler p = ∙∙-filler p refl

  ∙-filler-r : ∀{ℓ} {A : Type ℓ} {x y z : A} (p : x ＝ y) (q : y ＝ z)
             → Square (sym p) refl q (p ∙ q)
  ∙-filler-r p q i j = ∙-filler-l (sym q) (sym p) i (~ j)

opaque
  ∙-unique : ∀{ℓ} {A : Type ℓ} {x y z : A} {p : x ＝ y} {q : y ＝ z}
             (r : x ＝ z) (α : Square (sym p) q refl r)
           → r ＝ p ∙ q
  ∙-unique {p} {q} r α i = ∙∙-unique p q refl (r , α) (p ∙ q , ∙-filler p q) i .fst

-- Double composition agrees with iterated single composition
∙∙=∙ : ∀{ℓ} {A : Type ℓ}
       {w x : A} (p : x ＝ w) {y z : A} (r : y ＝ z) (q : w ＝ y)
     → p ∙∙ q ∙∙ r ＝ p ∙ (q ∙ r)
∙∙=∙ {A} p r q j i = hcomp (∂ i ∨ ∂ j) sys
  module ∙∙=∙-sys where
  sys : (k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) A
  sys k (i = i0) = p (~ k)
  sys k (i = i1) = ∙-filler-r q r j k
  sys k (j = i0) = ∙∙-filler p q r k i
  sys k (j = i1) = ∙-filler p (q ∙ r) k i
  sys k (k = i0) = q (~ j ∧ i)
{-# DISPLAY hcomp _ (∙∙=∙-sys.sys {ℓ} {A} {w} {x} p {y} {z} r q i) = ∙∙=∙ {ℓ} {A} {w} {x} p {y} {z} r q i #-}

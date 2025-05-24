{-# OPTIONS --safe #-}
module Foundations.Path.Base where

open import Prim.Data.Sigma
open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Foundations.Pi.Base

Square : {ℓ : Level} {A : Type ℓ}
         {w x : A} (p : w ＝ x) {y z : A} (r : y ＝ z)
         (q : w ＝ y) (s : x ＝ z)
       → Type ℓ
Square p r q s = Pathᴾ (λ i → p i ＝ r i) q s

refl : {ℓ : Level} {A : Type ℓ} {x : A} → x ＝ x
refl {x} _ = x

sym : {ℓ : Level} {A : Type ℓ} {x y : A} → x ＝ y → y ＝ x
sym p i = p (~ i)

-- double whiskering
infix 60 _∙∙_∙∙_
_∙∙_∙∙_ : {ℓ : Level} {A : I → Type ℓ}
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
  ∙∙-filler : {ℓ : Level} {A : I → Type ℓ}
              {w x : A i0} (p : x ＝ w) {y z : A i1} (q : Pathᴾ A w y) (r : y ＝ z)
            → Pathᴾ (λ i → Pathᴾ A (p (~ i)) (r i)) q (p ∙∙ q ∙∙ r)
  ∙∙-filler p q r k i = hfill (∂ i) k (∙∙-sys.sys p q r i)

opaque
  ∙∙-unique : {ℓ : Level} {A : Type ℓ}
              {w x : A} (p : x ＝ w) {y z : A} (r : y ＝ z) (q : w ＝ y)
              (α β : Σₜ (x ＝ z) λ s → Square (sym p) r q s)
            → α ＝ β
  ∙∙-unique {w} {x} p {y} {z} r q (α , α-fill) (β , β-fill) i = cube i i1 , λ j → cube i j where
    cube : (i j : I) → p (~ j) ＝ r j
    cube i j k = hfill (∂ i ∨ ∂ k) j λ where
      j (i = i0) → α-fill j k
      j (i = i1) → β-fill j k
      j (k = i0) → p (~ j)
      j (k = i1) → r j
      j (j = i0) → q k

opaque
  ∙∙-contract : {ℓ : Level} {A : Type ℓ}
                {w x : A} (p : x ＝ w) {y z : A} (r : y ＝ z) (q : w ＝ y)
                (β : Σₜ (x ＝ z) λ s → Square (sym p) r q s)
              → (p ∙∙ q ∙∙ r , ∙∙-filler p q r) ＝ β
  ∙∙-contract p r q = ∙∙-unique p r q _


-- For single homogenous path composition, we take `refl` as the top side:
infixr 90 _∙_
opaque
  _∙_ : {ℓ : Level} {A : Type ℓ} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
  p ∙ q = p ∙∙ refl ∙∙ q

  ∙-filler-l : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ＝ y) (q : y ＝ z)
             → Square refl q p (p ∙ q)
  ∙-filler-l {A} {y} p q i j = hcomp (~ i ∨ ∂ j) sys
    module ∙-filler-l-sys where
    sys : (k : I) → Partial (~ i ∨ ∂ j ∨ ~ k) A
    sys k (i = i0) = p (j ∨ ~ k)
    sys k (j = i0) = p (~ k)
    sys k (j = i1) = q (i ∧ k)
    sys k (k = i0) = y
  {-# DISPLAY hcomp _ (∙-filler-l-sys.sys {ℓ} {A} {x} {y} {z} p q i j) = ∙-filler-l {ℓ} {A} {x} {y} {z} p q i j #-}

  ∙-filler : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ＝ y) (q : y ＝ z)
           → Square (sym p) q refl (p ∙ q)
  ∙-filler p = ∙∙-filler p refl

  ∙-filler-r : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ＝ y) (q : y ＝ z)
             → Square (sym p) refl q (p ∙ q)
  ∙-filler-r p q i j = ∙-filler-l (sym q) (sym p) i (~ j)

opaque
  ∙-unique : {ℓ : Level} {A : Type ℓ} {x y z : A} {p : x ＝ y} {q : y ＝ z}
             (r : x ＝ z) (α : Square (sym p) q refl r)
           → r ＝ p ∙ q
  ∙-unique {p} {q} r α i = ∙∙-unique p q refl (r , α) (_ , ∙-filler p q) i .fst

-- Double composition agrees with iterated single composition
∙∙=∙ : {ℓ : Level} {A : Type ℓ}
       {w x : A} (p : x ＝ w) {y z : A} (r : y ＝ z) (q : w ＝ y)
     → p ∙∙ q ∙∙ r ＝ p ∙ q ∙ r
∙∙=∙ {A} p r q j i = hcomp (∂ i ∨ ∂ j) sys
  module ∙∙=∙-sys where
  sys : (k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) A
  sys k (i = i0) = p (~ k)
  sys k (i = i1) = ∙-filler-r q r j k
  sys k (j = i0) = ∙∙-filler p q r k i
  sys k (j = i1) = ∙-filler p (q ∙ r) k i
  sys k (k = i0) = q (~ j ∧ i)
{-# DISPLAY hcomp _ (∙∙=∙-sys.sys {ℓ} {A} {w} {x} p {y} {z} r q i) = ∙∙=∙ {ℓ} {A} {w} {x} p {y} {z} r q i #-}

opaque
  ap-comp-∙ : {ℓa ℓb : Level} {A : Type ℓa} {B : Type ℓb}
              (f : A → B)
              {x y z : A} (p : x ＝ y) (q : y ＝ z)
            → ap f (p ∙ q) ＝ ap f p ∙ ap f q
  ap-comp-∙ f p q i = ∙∙-unique (ap f p) (ap f q) refl
    (ap f (p ∙ q)    , λ k j → f (∙-filler p q k j))
    (ap f p ∙ ap f q , ∙-filler (ap f p) (ap f q))
    i .fst


-- Useful gadget

record Recall {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′}
  (f : (x : A) → B x) (x : A) (y : B x) : Type (ℓ l⊔ ℓ′) where
  constructor mk-recall
  field recall-eq : f x ＝ y

recall : {ℓ ℓ′ : Level} {A : Type ℓ} {B : A → Type ℓ′}
         (f : (x : A) → B x) (x : A)
       → Recall f x (f x)
recall f x = mk-recall (λ _ → f x)

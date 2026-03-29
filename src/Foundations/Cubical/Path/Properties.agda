module Foundations.Cubical.Path.Properties where

open import Prim.Data.Sigma
open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Foundations.Cubical.Path.Base

opaque
  ap-comp-∙ : ∀{ℓa ℓb} {A : Type ℓa} {B : Type ℓb}
              (f : A → B)
              {x y z : A} (p : x ＝ y) (q : y ＝ z)
            → ap f (p ∙ q) ＝ ap f p ∙ ap f q
  ap-comp-∙ f p q i = ∙∙-unique (ap f p) (ap f q) refl
    (ap f (p ∙ q)    , λ k j → f (∙-filler p q k j))
    (ap f p ∙ ap f q , ∙-filler (ap f p) (ap f q))
    i .fst

opaque
  unfolding _∙_
  sym-∙ : ∀{ℓ} {A : Type ℓ}
          {x y z : A} (p : x ＝ y) (q : y ＝ z)
        → sym (p ∙ q) ＝ sym q ∙ sym p
  sym-∙ p q _ j = (p ∙ q) (~ j)

opaque
  id-o : ∀{ℓ} {A : Type ℓ} {x y : A} (p : x ＝ y)
       → p ∙ refl ＝ p
  id-o p = sym (∙-filler-l p refl)

opaque
  id-i : ∀{ℓ} {A : Type ℓ} {x y : A} (p : x ＝ y)
       → refl ∙ p ＝ p
  id-i p = sym (∙-filler-r refl p)

opaque
  unfolding _∙_
  assoc : ∀{ℓ} {A : Type ℓ}
          {w x y z : A} (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
        → p ∙ (q ∙ r) ＝ (p ∙ q) ∙ r
  assoc p q r i = ∙-filler-l p q i ∙ ∙-filler-r q r (~ i)

opaque
  unfolding _∙_
  path-inv : ∀{ℓ} {A : Type ℓ} {x y : A} (p : x ＝ y)
           → sym p ∙ p ＝ refl
  path-inv p i j = hcomp (i ∨ ∂ j) (λ k _ → p (k ∨ i))


-- Square manipulation

magic-square : ∀{ℓ} {A : Type ℓ} {x y z : A} (p : x ＝ y) (q : y ＝ z) → Square p q p q
magic-square p q j i = hcomp (∂ i ∨ ∂ j) λ where
  k (i = i0) → p j
  k (i = i1) → q (j ∧ k)
  k (j = i0) → p i
  k (j = i1) → q (i ∧ k)
  k (k = i0) → p (i ∨ j)


commutes→square : ∀{ℓ} {A : Type ℓ} {w x y z : A}
                  {p : w ＝ x} {q : w ＝ y} {r : y ＝ z} {s : x ＝ z}
                → p ∙ s ＝ q ∙ r
                → Square p r q s
commutes→square {A} {p} {q} {r} {s} θ i j = hcomp (∂ i ∨ ∂ j) sys
  module commutes→square-sys where
  sys : (k : I) → Partial (~ k ∨ ∂ i ∨ ∂ j) A
  sys k (k = i0) = θ j i
  sys k (i = i0) = q (  k ∧ j)
  sys k (i = i1) = s (~ k ∨ j)
  sys k (j = i0) = ∙-filler-l p s (~ k) i
  sys k (j = i1) = ∙-filler-r q r (~ k) i
{-# DISPLAY hcomp _ (commutes→square-sys.sys {ℓ} {A} {w} {x} {y} {z} {p} {q} {r} {s} θ i j) =
  commutes→square {ℓ} {A} {w} {x} {y} {z} {p} {q} {r} {s} θ i j #-}

square→commutes : ∀{ℓ} {A : Type ℓ} {w x y z : A}
                  {p : w ＝ x} {q : w ＝ y} {r : y ＝ z} {s : x ＝ z}
                → Square p r q s
                → p ∙ s ＝ q ∙ r
square→commutes {A} {p} {q} {r} {s} α i j = hcomp (∂ i ∨ ∂ j) sys
  module square→commutes-sys where
  sys : (k : I) → Partial (~ k ∨ ∂ i ∨ ∂ j) A
  sys k (k = i0) = α j i
  sys k (i = i0) = ∙-filler-l p s k j
  sys k (i = i1) = ∙-filler-r q r k j
  sys k (j = i0) = q (~ k ∧ i)
  sys k (j = i1) = s (  k ∨ i)
{-# DISPLAY hcomp _ (square→commutes-sys.sys {ℓ} {A} {w} {x} {y} {z} {p} {q} {r} {s} α i j) =
  square→commutes {ℓ} {A} {w} {x} {y} {z} {p} {q} {r} {s} α i j #-}

opaque
  square→conjugate
    : ∀{ℓ} {A : Type ℓ} {w x y z : A}
      {p : x ＝ y} {q : x ＝ z} {r : z ＝ w} {s : y ＝ w}
    → Square p r q s
    → s ＝ sym p ∙ (q ∙ r)
  square→conjugate {p} {q} {r} {s} θ = sym (ap fst (∙∙-contract (sym p) r q (s , θ))) ∙ ∙∙=∙ (sym p) r q

-- TODO
-- opaque
--   conjugate→square
--     : ∀{ℓ} {A : Type ℓ} {w x y z : A}
--       {p : x ＝ y} {q : x ＝ z} {r : z ＝ w} {s : y ＝ w}
--     → s ＝ sym p ∙ (q ∙ r)
--     → Square p r q s
--   conjugate→square {p} {q} {r} {s} u = to-pathᴾ (transport-path q p r ∙ sym u)


-- Homotopy

homotopy-invert : ∀{ℓ} {A : Type ℓ} {f : A → A}
                → (H : (x : A) → f x ＝ x) {x : A}
                → H (f x) ＝ ap f (H x)
homotopy-invert {A} {f} H {x} i j = hcomp (∂ i ∨ ∂ j) sys
  module homotopy-invert-sys where
  sys : (k : I) → Partial (~ k ∨ ∂ j ∨ ∂ i) A
  sys k (k = i0) = H x       (j ∧ i)
  sys k (j = i0) = H (f x)   (~ k)
  sys k (j = i1) = H x       (~ k ∧ i)
  sys k (i = i0) = H (f x)   (~ k ∨ j)
  sys k (i = i1) = H (H x j) (~ k)
{-# DISPLAY hcomp _ (homotopy-invert-sys.sys {ℓ} {A} {f} H {x} i j) =
  homotopy-invert {ℓ} {A} {f} H {x} i j #-}

opaque
  homotopy-natural : ∀{ℓa ℓb} {A : Type ℓa} {B : Type ℓb}
                     {f g : A → B}
                     (H : (a : A) → f a ＝ g a)
                     {x y : A} (p : x ＝ y)
                   → H x ∙ ap g p ＝ ap f p ∙ H y
  homotopy-natural {A} {B} {f} {g} H {x} {y} p = square→commutes λ j i → hcomp (∂ i ∨ ∂ j) (sys i j)
    module homotopy-natural-sys where
    sys : (i j k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) B
    sys i j k (i = i0) = H x           (j ∧ k)
    sys i j k (i = i1) = H (p k)       (j ∧ k)
    sys i j k (j = i0) = f (p (i ∧ k))
    sys i j k (j = i1) = H (p (i ∧ k)) k
    sys i j k (k = i0) = f x

homotopy-sym-inv : ∀{ℓ} {A : Type ℓ} {f : A → A}
                   (H : (a : A) → f a ＝ a)
                   (x : A)
                 → Path (f x ＝ f x) (λ i → H (H x (~ i)) i) refl
homotopy-sym-inv {A} {f} H x i j = hcomp (∂ i ∨ ∂ j) sys
  module homotopy-sym-inv-sys where
  sys : (k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) A
  sys k (i = i0) = H (H x (~ j)) j
  sys k (i = i1) = H x (j ∧ ~ k)
  sys k (j = i0) = f x
  sys k (j = i1) = H x (i ∧ ~ k)
  sys k (k = i0) = H (H x (i ∨ ~ j)) j
{-# DISPLAY hcomp _ (homotopy-sym-inv-sys.sys {ℓ} {A} {f} H x i j) =
  homotopy-sym-inv {ℓ} {A} {f} H x i j #-}

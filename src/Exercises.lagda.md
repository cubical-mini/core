```agda

module Exercises where

open import Prim.Prelude
open import Lib.Path.Base

Square' : ∀ {ℓ} {A : Type ℓ}
  {a00 a01 : A} (p : a00 ＝ a01)
  {a10 a11 : A} (q : a10 ＝ a11)
  (r : a00 ＝ a10) (s : a01 ＝ a11)
  → Type _
Square' p q r s = PathP (λ i → r i ＝ s i) p q

Square'' : ∀ {ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
  → a00 ＝ a01 → a00 ＝ a10 → a01 ＝ a11 → a10 ＝ a11
  → Type ℓ
Square'' p q r s = PathP (λ i → q i ＝ r i) p s


fillSquare : ∀ {ℓ} {A : Type ℓ} {a b c d : A}
           → Path A a b → Path A b d → Path A a c
           → Path A c d
fillSquare p q r i = hfill i i λ where
  j (i = i1) → q j
  j (j = i0) → (sym r ∙ p) i

myInvPath : ∀ {ℓ} {A : Type ℓ} {x y : A} → Path A x y → Path A y x
myInvPath p i = hcomp (∂ i) λ where
  j (i = i0) → p j
  j (i = i1) → p (~ j)
  j (j = i0) → p i

∙-idr : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ＝ y) → p ∙ refl ＝ p
∙-idr {x = x} {y} p = γ where
  γ : Square (erefl x) (p ∙ refl) p (erefl y)
  γ i j = hfill (∂ j) (~ i) λ where
    k (j = i0) → x
    k (j = i1) → y
    k (k = i0) → p j

  γ' : p ∙ refl ＝ p ／ p
  γ' i j = hfill (∂ j) (~ i) λ where
    k (j = i0) → x
    k (j = i1) → y
    k (k = i0) → p j

  Sq-eqv : Square' (p ∙ refl) p (erefl x) (erefl y) ＝ Square (erefl x) (p ∙ refl) p (erefl y)
  Sq-eqv = refl
  -- test : Square (erefl x) p p (erefl y)
  -- test = erefl p


```


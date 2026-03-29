module Foundations.Cubical.Path.Transport where

open import Prim.Data.Sigma
open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Foundations.Cubical.Path.Base
open import Foundations.Cubical.Path.Coe
open import Foundations.Cubical.Pi

transport : ∀{ℓ} {A B : Type ℓ} → A ＝ B → A → B
transport p = coe0→1 λ i → p i
{-# DISPLAY transp {ℓ} A i0 = transport {ℓ} {A i0} {A i1} A #-}

transport-refl : ∀{ℓ} {A : Type ℓ} (x : A) → transport refl x ＝ x
transport-refl x i = coe1→i _ i x

transport-filler : ∀{ℓ} {A B : Type ℓ} (p : A ＝ B) (x : A)
                 → Pathᴾ (λ i → p i) x (transport p x)
transport-filler p x i = coe0→i (λ j → p j) i x

transport-filler-ext : ∀{ℓ} {A B : Type ℓ} (p : A ＝ B)
                     → Pathᴾ (λ i → A → p i) id (transport p)
transport-filler-ext p i x = transport-filler p x i

transport⁻-filler-ext : ∀{ℓ} {A B : Type ℓ} (p : A ＝ B)
                      → Pathᴾ (λ i → p i → A) id (transport (sym p))
transport⁻-filler-ext p i = coei→0 (λ j → p j) i

transport⁻-transport : ∀{ℓ} {A B : Type ℓ} (p : A ＝ B) (a : A)
                     → transport (sym p) (transport p a) ＝ a
transport⁻-transport p a i =
  transport⁻-filler-ext p (~ i) (transport-filler-ext p (~ i) a)

transport-comp : ∀{ℓ} {A B C : Type ℓ} (p : A ＝ B) (q : B ＝ C) (x : A)
               → transport (p ∙ q) x ＝ transport q (transport p x)
transport-comp p q x i = transport (∙-filler-r p q (~ i)) (transport-filler-ext p i x)

transport-flip : ∀{ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1}
               → x ＝ transport (λ i → A (~ i)) y
               → transport (λ i → A i) x ＝ y
transport-flip {A} {y} p =
  ap (transport (λ i → A i)) p ∙ transport⁻-transport (λ i → A (~ i)) y

opaque
  transport-path : ∀{ℓ} {A : Type ℓ}
                   {x y x′ y′ : A} (p : x ＝ y) (left : x ＝ x′) (right : y ＝ y′)
                 → transport (λ i → left i ＝ right i) p ＝ sym left ∙ (p ∙ right)
  transport-path {A} p left right = lemma ∙ ∙∙=∙ (sym left) right p
    where
    lemma : transport (λ i → left i ＝ right i) p ＝ sym left ∙∙ p ∙∙ right
    lemma i j = hcomp (~ i ∨ ∂ j) λ where
      k (k = i0) → coei→1 (λ _ → A) i (p j)
      k (i = i0) → hfill (∂ j) k λ where
        k (k = i0) → coe0→1 (λ _ → A) (p j)
        k (j = i0) → coei→1 (λ _ → A) k (left k)
        k (j = i1) → coei→1 (λ _ → A) k (right k)
      k (j = i0) → coei→1 (λ _ → A) (k ∨ i) (left k)
      k (j = i1) → coei→1 (λ _ → A) (k ∨ i) (right k)


-- Pathᴾ conversion

pathᴾ=path : ∀{ℓ} (P : I → Type ℓ) (p : P i0) (q : P i1)
           →  Pathᴾ P p q
           ＝ (transport (λ i → P i) p ＝ q)
pathᴾ=path P p q i = Pathᴾ (λ j → P (i ∨ j)) (transport-filler (λ j → P j) p i) q

pathᴾ=path⁻ : ∀{ℓ} (P : I → Type ℓ) (p : P i0) (q : P i1)
            →  Pathᴾ P p q
            ＝ (p ＝ transport (λ i → P (~ i)) q)
pathᴾ=path⁻ P p q i = Pathᴾ (λ j → P (~ i ∧ j)) p (transport-filler (λ j → P (~ j)) q i)

module _ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1} where
  -- to-pathᴾ : (transport (λ i → A i) x ＝ y) → ＜ x ／ A ＼ y ＞
  to-pathᴾ : (coe0→1 A x ＝ y) → Pathᴾ A x y
  to-pathᴾ p i = hcomp (∂ i) sys
    module to-pathᴾ-sys where
    sys : (j : I) → Partial (∂ i ∨ ~ j) (A i)
    sys j (i = i0) = x
    sys j (i = i1) = p j
    sys j (j = i0) = coe0→i A i x

  -- from-pathᴾ : ＜ x ／ A ＼ y ＞ → transport (λ i → A i) x ＝ y
  opaque
    from-pathᴾ : Pathᴾ A x y → coe0→1 A x ＝ y
    from-pathᴾ p i = coei→1 A i (p i)
{-# DISPLAY hcomp _ (to-pathᴾ-sys.sys {ℓ} {A} {x} {y} p i) = to-pathᴾ {ℓ} {A} {x} {y} p i #-}

module _ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1} where
  to-pathᴾ⁻ : x ＝ coe1→0 A y → Pathᴾ A x y
  to-pathᴾ⁻ p i = to-pathᴾ {A = λ j → A (~ j)} (λ j → p (~ j)) (~ i)

  from-pathᴾ⁻ : Pathᴾ A x y → x ＝ coe1→0 A y
  from-pathᴾ⁻ p i = from-pathᴾ (λ j → p (~ j)) (~ i)

  opaque
    unfolding from-pathᴾ
    to-from-pathᴾ : (p : Pathᴾ A x y) → to-pathᴾ (from-pathᴾ p) ＝ p
    to-from-pathᴾ p i j = hcomp (i ∨ ∂ j) λ where
      k (i = i1) → transp (λ l → A (j ∧ (k ∨ l))) (~ j ∨ k) (p (j ∧ k)) -- TODO use `coe` ?
      k (j = i0) → x
      k (j = i1) → coei→1 A k (p k)
      k (k = i0) → coe0→i A j x

    from-to-pathᴾ : (p : coe0→1 A x ＝ y) → from-pathᴾ {A = A} (to-pathᴾ p) ＝ p
    from-to-pathᴾ p i j =
      hcomp (∂ i ∨ ∂ j) λ where
        k (k = i0) → coei→1 A (j ∨ ~ i) (transp (λ l → A (j ∨ (~ i ∧ l))) (i ∨ j) (coe0→i A j x)) -- TODO use `coe` ?

        k (j = i0) → slide (k ∨ ~ i)
        k (j = i1) → p k

        k (i = i0) → coei→1 A j (hfill (∂ j) k λ where
          k (k = i0) → coe0→i A j x
          k (j = i0) → x
          k (j = i1) → p k)

        k (i = i1) → hcomp (∂ k ∨ ∂ j) λ where
          l (l = i0) → slide (k ∨ j)
          l (k = i0) → slide j
          l (k = i1) → p (j ∧ l)
          l (j = i0) → slide k
          l (j = i1) → p (k ∧ l)
      where
        slide : coe0→1 A x ＝ coe0→1 A x
        slide i = coei→1 A i (coe0→i A i x)


-- Subst

subst : ∀{ℓa ℓb} {A : Type ℓa} (B : A → Type ℓb)
        {x y : A} (p : x ＝ y)
      → B x → B y
subst B p = transport (λ i → B (p i))

subst-refl : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb} {x : A} (px : B x) → subst B refl px ＝ px
subst-refl = transport-refl

subst-filler : ∀{ℓa ℓb} {A : Type ℓa} (B : A → Type ℓb) {x y : A} (p : x ＝ y) (b : B x)
             → Pathᴾ (λ i → B (p i)) b (subst B p b)
subst-filler B p = transport-filler (ap B p)

subst⁻-filler : ∀{ℓa ℓb} {A : Type ℓa} (B : A → Type ℓb) {x y : A} (p : x ＝ y) (b : B y)
              → Pathᴾ (λ i → B (p (~ i))) b (subst B (sym p) b)
subst⁻-filler B p = subst-filler B (sym p)

subst⁻-subst : ∀{ℓa ℓb} {A : Type ℓa} (B : A → Type ℓb) {x y : A} (p : x ＝ y)
             → (u : B x) → subst B (sym p) (subst B p u) ＝ u
subst⁻-subst B p u = transport⁻-transport (ap B p) u

subst-comp : ∀{ℓa ℓb} {A : Type ℓa} (B : A → Type ℓb)
             {x y z : A} (p : x ＝ y) (q : y ＝ z) (u : B x)
           → subst B (p ∙ q) u ＝ subst B q (subst B p u)
subst-comp B p q Bx i =
  transport (ap B (∙-filler-r p q (~ i))) (transport-filler-ext (ap B p) i Bx)

subst-slice : ∀{ℓa ℓb ℓc} {A : Type ℓa} (B : A → Type ℓb) (C : A → Type ℓc)
              (F : {a : A} → B a → C a)
              {x y : A} (p : x ＝ y) (b : B x)
            → subst C p (F b) ＝ F (subst B p b)
subst-slice B C F p b i = transport⁻-filler-ext (ap C (sym p)) (~ i) (F (transport-filler-ext (ap B p) i b))

subst-slice-filler : ∀{ℓa ℓb ℓc} {A : Type ℓa} (B : A → Type ℓb) (C : A → Type ℓc)
                     (F : {a : A} → B a → C a)
                     {x y : A} (p : x ＝ y)
                   → Pathᴾ (λ i → B (p i) → C (p i)) F (subst C p ∘ F ∘ subst B (sym p))
subst-slice-filler B C F p i b = transport-filler (ap C p) (F (transport⁻-filler-ext (ap B p) i b)) i

Σ-path : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
         {x y : Σ A B} (p : x .fst ＝ y .fst)
       → subst B p (x .snd) ＝ (y .snd)
       → x ＝ y
Σ-path p q = p ,ₚ to-pathᴾ q

opaque
  subst-path-left : ∀{ℓ} {A : Type ℓ}
                    {x y x′ : A} (p : x ＝ y) (left : x ＝ x′)
                  → subst (λ e → e ＝ y) left p ＝ sym left ∙ p
  subst-path-left {y} p left = transport-path p left refl ∙ ap (sym left ∙_) (sym (∙-filler-l p refl))

  subst-path-right : ∀{ℓ} {A : Type ℓ}
                     {x y y′ : A} (p : x ＝ y) (right : y ＝ y′)
                   → subst (λ e → x ＝ e) right p ＝ p ∙ right
  subst-path-right {x} p right = transport-path p refl right ∙ sym (∙-filler-r refl (p ∙ right))

  subst-path-both : ∀{ℓ} {A : Type ℓ}
                    {x x′ : A} (p : x ＝ x) (adj : x ＝ x′)
                  → subst (λ x → x ＝ x) adj p ＝ sym adj ∙ (p ∙ adj)
  subst-path-both p adj = transport-path p adj adj


subst² : ∀{ℓa ℓb ℓc} {A : Type ℓa} {B : A → Type ℓb} (C : (a : A) → B a → Type ℓc)
          {x y : A} (p : x ＝ y) {z : B x} {w : B y} (q : Pathᴾ (λ i → B (p i)) z w)
        → C x z → C y w
subst² C p q = transport (λ i → C (p i) (q i))

subst²-filler : ∀{ℓa ℓb ℓc} {A : Type ℓa} {B : Type ℓb} (C : A → B → Type ℓc)
                {x y : A} (p : x ＝ y) {z w : B} (q : z ＝ w) (c : C x z)
              → Pathᴾ (λ i → C (p i) (q i)) c (subst² C p q c)
subst²-filler C p q = transport-filler (ap² C p q)

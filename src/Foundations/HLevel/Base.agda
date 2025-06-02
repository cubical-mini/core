{-# OPTIONS --safe #-}
module Foundations.HLevel.Base where

open import Prim.Data.Nat
open import Prim.Data.Sigma
open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Notation.Base

open import Foundations.Path.Groupoid.Base
open import Foundations.Path.Transport

record is-contr {ℓ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    centre : A
    paths  : (x : A) → centre ＝ x

open is-contr public

is-prop : ∀{ℓ} (A : Type ℓ) → Type ℓ
is-prop  A = (x y : A) → x ＝ y

HLevel : Type₀
HLevel = ℕ

-- TODO generalize to structures on hom types or use display?
_on-paths-of_ : ∀{ℓ ℓ′} (S : Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ l⊔ ℓ′)
S on-paths-of A = (a a′ : A) → S (a ＝ a′)

is-of-hlevel : ∀{ℓ} → HLevel → Type ℓ → Type ℓ
is-of-hlevel 0 A = is-contr A
is-of-hlevel 1 A = is-prop  A
is-of-hlevel (suc (suc h)) A = is-of-hlevel (suc h) on-paths-of A

is-set is-groupoid is-2-groupoid : ∀{ℓ} → Type ℓ → Type ℓ
is-set = is-of-hlevel 2
is-groupoid = is-of-hlevel 3
is-2-groupoid = is-of-hlevel 4


-- Essential properties of `is-prop` and `is-contr`

is-prop→pathᴾ : {ℓ : Level} {B : I → Type ℓ}
                (h : (i : I) → is-prop (B i))
              → (b₀ : B i0) (b₁ : B i1)
              → Pathᴾ B b₀ b₁
is-prop→pathᴾ h b₀ b₁ = to-pathᴾ (h i1 _ b₁)

is-contr→is-prop : ∀{ℓ} {A : Type ℓ} → is-contr A → is-prop A
is-contr→is-prop {A} A-c x y i = hcomp (∂ i) sys
  module is-contr→is-prop-sys where
  sys : (j : I) → Partial (∂ i ∨ ~ j) A
  sys j (i = i0) = A-c .paths x j
  sys j (i = i1) = A-c .paths y j
  sys j (j = i0) = A-c .centre
{-# DISPLAY hcomp _ (is-contr→is-prop-sys.sys {ℓ} {A} A-c x y i) = is-contr→is-prop {ℓ} {A} A-c x y i #-}

contractible-if-inhabited : ∀{ℓ} {A : Type ℓ} → (A → is-contr A) → is-prop A
contractible-if-inhabited cont x y = is-contr→is-prop (cont x) x y

is-prop→is-set : ∀{ℓ} {A : Type ℓ} → is-prop A → is-set A
is-prop→is-set {A} h a b p q j i = hcomp (∂ i ∨ ∂ j) sys
  module is-prop→is-set-sys where
  sys : (k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) A
  sys k (i = i0) = h a a k
  sys k (i = i1) = h a b k
  sys k (j = i0) = h a (p i) k
  sys k (j = i1) = h a (q i) k
  sys k (k = i0) = a
{-# DISPLAY hcomp _ (is-prop→is-set-sys.sys {ℓ} {A} h a b p q j i) = is-prop→is-set {ℓ} {A} h a b p q i j #-}

is-of-hlevel-suc : ∀{ℓ} {A : Type ℓ} (h : HLevel) → is-of-hlevel h A → is-of-hlevel (suc h) A
is-of-hlevel-suc 0 x = is-contr→is-prop x
is-of-hlevel-suc 1 x = is-prop→is-set x
is-of-hlevel-suc (suc (suc h)) p x y = is-of-hlevel-suc (suc h) (p x y)

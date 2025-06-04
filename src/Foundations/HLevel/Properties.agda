{-# OPTIONS --safe #-}
module Foundations.HLevel.Properties where

open import Prim.Data.Nat
open import Prim.Interval
open import Prim.Type

open import Notation.Composition
open import Notation.Displayed.Total
open import Notation.Reflexivity
open import Notation.Symmetry

open import Foundations.HLevel.Base
open import Foundations.Path.Groupoid
open import Foundations.Path.Transport
open import Foundations.Singleton

open Path-gpd0

is-prop→pathᴾ : {ℓ : Level} {B : I → Type ℓ}
                (h : (i : I) → is-prop (B i))
              → (b₀ : B i0) (b₁ : B i1)
              → Pathᴾ B b₀ b₁
is-prop→pathᴾ h b₀ b₁ = to-pathᴾ (h i1 _ b₁)

is-contr→is-prop : ∀{ℓ} {A : Type ℓ} → is-contr A → is-prop A
is-contr→is-prop {A} A-c x y i = hcomp (∂ i) sys
  module is-contr→is-prop-sys where
  sys : (j : I) → Partial (∂ i ∨ ~ j) A
  sys j (i = i0) = paths A-c x j
  sys j (i = i1) = paths A-c y j
  sys j (j = i0) = centre A-c
{-# DISPLAY hcomp _ (is-contr→is-prop-sys.sys {ℓ} {A} A-c x y i) = is-contr→is-prop {ℓ} {A} A-c x y i #-}

contractible-if-inhabited : ∀{ℓ} {A : Type ℓ} → (A → is-contr A) → is-prop A
contractible-if-inhabited cont x y = is-contr→is-prop (cont x) x y

inhabited-prop-is-contr : ∀{ℓ} {A : Type ℓ} → A → is-prop A → is-contr A
inhabited-prop-is-contr x p .carrier = x
inhabited-prop-is-contr x p .structured = p (inhabited-prop-is-contr x p .carrier)

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

is-of-hlevel-+ : ∀{ℓ} {A : Type ℓ} (h₀ h₁ : HLevel)
               → is-of-hlevel h₀ A → is-of-hlevel (h₁ + h₀) A
is-of-hlevel-+ h₀ 0     x = x
is-of-hlevel-+ h₀ (suc h₁) x = is-of-hlevel-suc (h₁ + h₀) (is-of-hlevel-+ h₀ h₁ x)

is-of-hlevel-+-left : ∀{ℓ} {A : Type ℓ} (h₀ h₁ : HLevel)
                    → is-of-hlevel h₀ A → is-of-hlevel (h₀ + h₁) A
is-of-hlevel-+-left {A} h₀ h₁ A-hl =
  subst (λ h → is-of-hlevel h A) (+-comm h₀ h₁) (is-of-hlevel-+ h₀ h₁ A-hl) where
    +-comm : ∀ n k → k + n ＝ n + k
    +-comm 0 k = go k where
      go : ∀ k → k + 0 ＝ k
      go zero = refl
      go (suc x) = ap suc (go x)
    +-comm (suc n) k = go n k ∙ ap suc (+-comm n k) where
      go : ∀ n k → k + suc n ＝ suc (k + n)
      go n zero = refl
      go n (suc k) = ap suc (go n k)

opaque
  is-contr→is-set : ∀{ℓ} {A : Type ℓ} → is-contr A → is-set A
  is-contr→is-set = is-of-hlevel-+-left 0 2

  is-prop→is-of-hlevel-suc : ∀{ℓ} {A : Type ℓ} {h : HLevel} → is-prop A → is-of-hlevel (suc h) A
  is-prop→is-of-hlevel-suc {h = 0    } A-prop = A-prop
  is-prop→is-of-hlevel-suc {h = suc h} A-prop =
    is-of-hlevel-suc (suc h) (is-prop→is-of-hlevel-suc {h = h} A-prop)

  path-is-of-hlevel-same : ∀{ℓ} {A : Type ℓ} (h : HLevel) → is-of-hlevel h A → {x y : A}
                         → is-of-hlevel h (x ＝ y)
  path-is-of-hlevel-same 0 ahl = inhabited-prop-is-contr
    (is-contr→is-prop ahl _ _)
    (is-prop→is-set (is-contr→is-prop ahl) _ _)
  path-is-of-hlevel-same (suc h) ahl = is-of-hlevel-suc (suc h) ahl _ _

  pathᴾ-is-of-hlevel-same : ∀{ℓ} {A : Type ℓ} {A : I → Type ℓ} (h : HLevel)
                          → is-of-hlevel h (A i1)
                          → {x : A i0} {y : A i1}
                          → is-of-hlevel h (Pathᴾ A x y)
  pathᴾ-is-of-hlevel-same {A} h ahl {x} {y} =
    subst (is-of-hlevel h) (sym (pathᴾ=path _ x y)) (path-is-of-hlevel-same h ahl)

path-is-of-hlevel : ∀{ℓ} {A : Type ℓ} (h : HLevel) → is-of-hlevel (suc h) A → (x y : A) → is-of-hlevel h (x ＝ y)
path-is-of-hlevel 0 ahl x y .carrier = ahl x y
path-is-of-hlevel 0 ahl x y .structured = is-prop→is-set ahl x y _
path-is-of-hlevel (suc h) ahl x y = ahl x y

pathᴾ-is-of-hlevel : ∀{ℓ} {A : I → Type ℓ} (h : HLevel)
                   → is-of-hlevel (suc h) (A i1)
                   → (x : A i0) (y : A i1)
                   → is-of-hlevel h (Pathᴾ A x y)
pathᴾ-is-of-hlevel {A} h ahl x y =
  subst (is-of-hlevel h) (sym (pathᴾ=path A x y)) (path-is-of-hlevel h ahl _ _)

opaque
  is-contr-is-prop : ∀{ℓ} {A : Type ℓ} → is-prop (is-contr A)
  is-contr-is-prop u v j .carrier = paths u (centre v) j
  is-contr-is-prop u v j .structured y i = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → paths u (paths u (centre v) j) k
    k (i = i1) → paths u y k
    k (j = i0) → paths u (paths u y i) k
    k (j = i1) → paths u (paths v y i) k
    k (k = i0) → centre u

  is-prop-is-prop : ∀{ℓ} {A : Type ℓ} → is-prop (is-prop A)
  is-prop-is-prop f g i a b = is-prop→is-set f a b (f a b) (g a b) i

  is-of-hlevel-is-prop : ∀{ℓ} {A : Type ℓ} (h : HLevel) → is-prop (is-of-hlevel h A)
  is-of-hlevel-is-prop 0 = is-contr-is-prop
  is-of-hlevel-is-prop (suc 0) = is-prop-is-prop
  is-of-hlevel-is-prop (suc (suc h)) x y i a b =
    is-of-hlevel-is-prop (suc h) (x a b) (y a b) i

  is-of-hlevel-is-of-hlevel-suc : ∀{ℓ} {A : Type ℓ} {h : HLevel} (h₁ : HLevel)
                                → is-of-hlevel (suc h₁) (is-of-hlevel h A)
  is-of-hlevel-is-of-hlevel-suc {h} h₁ = is-of-hlevel-+-left 1 h₁ (is-of-hlevel-is-prop h)

opaque
  is-set→squareᴾ
    : ∀{ℓ} {A : I → I → Type ℓ}
      (A-set : (i j : I) → is-set (A i j))
      {w : A i0 i0} {x : A i0 i1} (p : Pathᴾ (λ j → A i0 j) w x)
      {y : A i1 i0} {z : A i1 i1} (r : Pathᴾ (λ j → A i1 j) y z)
      (q : Pathᴾ (λ i → A i i0) w y) (s : Pathᴾ (λ i → A i i1) x z)
    → Squareᴾ A p r q s
  is-set→squareᴾ A-set p r q s =
    transport (sym (pathᴾ=path _ q s)) (pathᴾ-is-of-hlevel 1 (A-set i1 i1) (p i1) (r i1) _ s)

opaque
  is-prop→squareᴾ
    : ∀{ℓ} {A : I → I → Type ℓ}
      (A-prop : (i j : I) → is-prop (A i j))
      {w : A i0 i0} {x : A i0 i1} (p : Pathᴾ (λ j → A i0 j) w x)
      {y : A i1 i0} {z : A i1 i1} (r : Pathᴾ (λ j → A i1 j) y z)
      (q : Pathᴾ (λ i → A i i0) w y) (s : Pathᴾ (λ i → A i i1) x z)
    → Squareᴾ A p r q s
  is-prop→squareᴾ A-prop = is-set→squareᴾ (λ i j → is-prop→is-set (A-prop i j))

-- TODO restore if needed
-- is-set→cast-pathᴾ
--   : ∀{ℓa ℓp} {A : Type ℓa}{x y : A} {p q : x ＝ y} (P : A → Type ℓp) {px : P x} {py : P y}
--   → is-set A
--   → Pathᴾ (λ i → P (p i)) px py
--   → Pathᴾ (λ i → P (q i)) px py
-- is-set→cast-pathᴾ {p} {q} P {px} {py} A-set =
--   transport (λ j → Pathᴾ (λ i → P (A-set _ _ p q j i)) px py)

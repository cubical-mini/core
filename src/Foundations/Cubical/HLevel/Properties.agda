module Foundations.Cubical.HLevel.Properties where

open import Prim.Interval
open import Prim.Kan

open import Foundations.Base
open import Foundations.Cubical.HLevel.Base
open import Foundations.Cubical.Path.Base
open import Foundations.Cubical.Path.Coe
open import Foundations.Cubical.Path.Properties
open import Foundations.Cubical.Path.Transport

opaque
  is-contr→extend : ∀{ℓ} {A : Type ℓ} → is-contr A → (φ : I) (p : Partial φ A) → A [ φ ↦ p ]
  is-contr→extend C φ p = inS (hcomp φ
    λ { j (φ = i1) → C .snd (p 1=1) j
      ; j (j = i0) → C .fst
      })

opaque
  extend→is-contr : ∀{ℓ} {A : Type ℓ} (ext : ∀ φ (p : Partial φ A) → A [ φ ↦ p ]) → is-contr A
  extend→is-contr ext .fst = outS (ext i0 λ ())
  extend→is-contr ext .snd x i = outS (ext i λ _ → x)

inhabited-prop-is-contr : ∀{ℓ} {A : Type ℓ} → A → is-prop A → is-contr A
inhabited-prop-is-contr x p = x , p x

is-contr→is-prop : ∀{ℓ} {A : Type ℓ} → is-contr A → is-prop A
is-contr→is-prop (_ , paths) x y = sym (paths x) ∙ paths y

contractible-if-inhabited : ∀{ℓ} {A : Type ℓ} → (A → is-contr A) → is-prop A
contractible-if-inhabited cont x y = is-contr→is-prop (cont x) x y

opaque
  is-prop→is-set : ∀{ℓ} {A : Type ℓ} → is-prop A → is-set A
  is-prop→is-set h a b p q j i = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → h a a k
    k (i = i1) → h a b k
    k (j = i0) → h a (p i) k
    k (j = i1) → h a (q i) k
    k (k = i0) → a

is-prop→hlevel-1 : ∀{ℓ} {A : Type ℓ} → is-prop A → is-of-hlevel 1 A
is-prop→hlevel-1 pr x y .fst = pr x y
is-prop→hlevel-1 pr x y .snd = is-prop→is-set pr x y (pr x y)

is-of-hlevel-suc : ∀{ℓ} {A : Type ℓ} (h : HLevel) → is-of-hlevel h A → is-of-hlevel (suc h) A
is-of-hlevel-suc 0 cont = is-prop→hlevel-1 (is-contr→is-prop cont)
is-of-hlevel-suc (suc h) p x y = is-of-hlevel-suc h (p x y)

is-of-hlevel-+ : ∀{ℓ} {A : Type ℓ} (h₀ h₁ : HLevel) → is-of-hlevel h₀ A → is-of-hlevel (h₁ + h₀) A
is-of-hlevel-+ h₀ 0 hl = hl
is-of-hlevel-+ h₀ (suc h₁) hl = is-of-hlevel-suc (h₁ + h₀) (is-of-hlevel-+ h₀ h₁ hl)

is-of-hlevel-+-l : ∀{ℓ} {A : Type ℓ} (h₀ h₁ : HLevel) → is-of-hlevel h₀ A → is-of-hlevel (h₀ + h₁) A
is-of-hlevel-+-l 0        0        hl = hl
is-of-hlevel-+-l 0        (suc h₁) hl = is-of-hlevel-suc h₁ (is-of-hlevel-+-l 0 h₁ hl)
is-of-hlevel-+-l (suc h₀) h₁       hl x y = is-of-hlevel-+-l h₀ h₁ (hl x y)

opaque
  pathᴾ-is-of-hlevel : ∀{ℓ} {A : I → Type ℓ} (h : HLevel)
                       (hl : is-of-hlevel (suc h) (A i1))
                       x y → is-of-hlevel h (Pathᴾ A x y)
  pathᴾ-is-of-hlevel {A} h hl x y = subst (is-of-hlevel h) (sym (pathᴾ=path A x y)) (hl _ _)

opaque
  is-contr-is-prop : ∀{ℓ} {A : Type ℓ} → is-prop (is-contr A)
  is-contr-is-prop (c₀ , h₀) (c₁ , h₁) j .fst = h₀ c₁ j
  is-contr-is-prop (c₀ , h₀) (c₁ , h₁) j .snd y i = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → h₀ (h₀ c₁ j) k
    k (i = i1) → h₀ y k
    k (j = i0) → h₀ (h₀ y i) k
    k (j = i1) → h₀ (h₁ y i) k
    k (k = i0) → c₀

-- TODO move to documentation
opaque
  is-prop-is-prop : ∀{ℓ} {A : Type ℓ} → is-prop (is-prop A)
  is-prop-is-prop f g i a b = is-prop→is-set f a b (f a b) (g a b) i

opaque
  is-of-hlevel-is-prop : ∀{ℓ} {A : Type ℓ} (h : HLevel) → is-prop (is-of-hlevel h A)
  is-of-hlevel-is-prop 0 = is-contr-is-prop
  is-of-hlevel-is-prop (suc h) u v i x y = is-of-hlevel-is-prop h (u x y) (v x y) i

is-prop→pathᴾ : ∀{ℓ} {B : I → Type ℓ}
                (h : (i : I) → is-prop (B i))
                b₀ b₁ → Pathᴾ B b₀ b₁
is-prop→pathᴾ h b₀ b₁ = to-pathᴾ (h i1 _ b₁)

opaque
  is-set→squareᴾ
    : ∀{ℓ} {A : I → I → Type ℓ}
      (is-set : (i j : I) → is-set (A i j)) {w x y z}
      (p : Pathᴾ (λ j → A i0 j) w x) (r : Pathᴾ (λ j → A i1 j) y z)
      (q : Pathᴾ (λ i → A i i0) w y) (s : Pathᴾ (λ i → A i i1) x z)
    → Squareᴾ A p r q s
  is-set→squareᴾ is-set p r q s =
    transport (sym (pathᴾ=path _ _ _)) (pathᴾ-is-of-hlevel 1 (λ a b → is-prop→hlevel-1 (is-set i1 i1 a b)) _ _ _ _ .fst)

  is-prop→squareᴾ
    : ∀{ℓ} {A : I → I → Type ℓ}
      (pr : (i j : I) → is-prop (A i j)) {w x y z}
      (p : Pathᴾ (λ j → A i0 j) w x) (r : Pathᴾ (λ j → A i1 j) y z)
      (q : Pathᴾ (λ i → A i i0) w y) (s : Pathᴾ (λ i → A i i1) x z)
    → Squareᴾ A p r q s
  is-prop→squareᴾ pr = is-set→squareᴾ λ i j → is-prop→is-set (pr i j)


-- Automation

hlevel-basic-instance : ∀ n {ℓ} {A : Type ℓ} → is-of-hlevel n A → ∀ {k} → H-Level (n + k) A
hlevel-basic-instance n hl .H-Level.has-hlevel = is-of-hlevel-+-l n _ hl

hlevel-prop-instance : ∀ {n} {ℓ} {A : Type ℓ} → is-prop A → H-Level (suc n) A
hlevel-prop-instance A-pr .H-Level.has-hlevel = is-of-hlevel-+-l 1 _ (is-prop→hlevel-1 A-pr)

hlevel-set-instance : ∀ {n} {ℓ} {A : Type ℓ} → is-set A → H-Level (2 + n) A
hlevel-set-instance A-set .H-Level.has-hlevel = is-of-hlevel-+-l 2 _ λ x y → is-prop→hlevel-1 (A-set x y)

hlevel-groupoid-instance : ∀ {n} {ℓ} {A : Type ℓ} → is-groupoid A → H-Level (3 + n) A
hlevel-groupoid-instance A-grpd .H-Level.has-hlevel = is-of-hlevel-+-l 3 _ λ x y p q → is-prop→hlevel-1 (A-grpd x y p q)

opaque
  H-Level-is-prop : ∀ {n} {ℓ} {A : Type ℓ} → is-prop (H-Level n A)
  H-Level-is-prop {n} u v i .H-Level.has-hlevel = is-of-hlevel-is-prop n (u .H-Level.has-hlevel) (v .H-Level.has-hlevel) i

instance
  H-Level-H-Level : ∀ {h h₁} {ℓ} {A : Type ℓ} → H-Level (suc h) (H-Level h₁ A)
  H-Level-H-Level = hlevel-prop-instance H-Level-is-prop

-- FIXME MOVE should be auto solvable
prop! : ∀{ℓ} {A : I → Type ℓ} ⦃ pr : H-Level 1 (A i0) ⦄ {x y} → Pathᴾ A x y
prop! {A} ⦃ pr ⦄ {x} {y} = is-prop→pathᴾ (λ i → coe0→i (λ j → is-prop (A j)) i λ a b → pr .H-Level.has-hlevel a b .fst) x y



-- trash

is-contr→is-set : ∀{ℓ} {A : Type ℓ} → is-contr A → is-set A
is-contr→is-set cont x y p q = is-of-hlevel-+ 0 2 cont x y p q .fst
{-# WARNING_ON_USAGE is-contr→is-set "Deprecated: inline or use automation" #-}

path-is-of-hlevel-same : ∀ h {ℓ} {A : Type ℓ} {x y : A} → is-of-hlevel h A → is-of-hlevel h (x ＝ y)
path-is-of-hlevel-same h hl = is-of-hlevel-suc h hl _ _
{-# WARNING_ON_USAGE path-is-of-hlevel-same "Deprecated: inline" #-}

is-prop→is-of-hlevel-suc : ∀{ℓ} {A : Type ℓ} {h} → is-prop A → is-of-hlevel (suc h) A
is-prop→is-of-hlevel-suc {h} pr = is-of-hlevel-+-l 1 h (is-prop→hlevel-1 pr)
{-# WARNING_ON_USAGE is-prop→is-of-hlevel-suc "Deprecated: inline or use automation" #-}

path-is-of-hlevel : ∀{ℓ} {A : Type ℓ} (h : HLevel) → is-of-hlevel (suc h) A → (x y : A) → is-of-hlevel h (x ＝ y)
path-is-of-hlevel _ hl = hl
{-# WARNING_ON_USAGE path-is-of-hlevel "Deprecated: inline" #-}

is-of-hlevel-is-of-hlevel-suc : ∀{ℓ} {A : Type ℓ} {h} (h₁ : HLevel) → is-of-hlevel (suc h₁) (is-of-hlevel h A)
is-of-hlevel-is-of-hlevel-suc {h} h₁ = is-of-hlevel-+-l 1 h₁ (is-prop→hlevel-1 (is-of-hlevel-is-prop h))
{-# WARNING_ON_USAGE is-of-hlevel-is-of-hlevel-suc "Deprecated: inline or use automation" #-}

pathᴾ-is-of-hlevel-same : ∀{ℓ} {A : I → Type ℓ} (h : HLevel) (hl : is-of-hlevel h (A i1)) {x y} → is-of-hlevel h (Pathᴾ A x y)
pathᴾ-is-of-hlevel-same {A} h hl = pathᴾ-is-of-hlevel h (is-of-hlevel-suc h hl) _ _
{-# WARNING_ON_USAGE pathᴾ-is-of-hlevel-same "Deprecated: inline or use automation" #-}

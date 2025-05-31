{-# OPTIONS --safe #-}
module Foundations.HLevel.Base where

open import Prim.Data.Nat
open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Connected
open import Notation.Connected.Strict
open import Notation.Delooping
open import Notation.Strict
open import Notation.Thin

is-contr : {ℓ : Level} (A : Type ℓ) → Type ℓ
is-contr A = Connected (𝑩 A) Strict lzero lzero
{-# DISPLAY Connected {_} {_} {_} (𝑩 A) Strict _ _ = is-contr A #-}

is-contr⁻ : {ℓ : Level} (A : Type ℓ) → Type ℓ
is-contr⁻ A = Connected (𝑩 A) (Strict ²ᵒᵖω) lzero lzero
{-# DISPLAY Connected {_} {_} {_} (𝑩 A) (_²ᵒᵖω Strict) _ _ = is-contr⁻ A #-}

module _ {ℓ : Level} {A : Type ℓ} where
  paths : ⦃ A-c : is-contr A ⦄ (x : A) → centre ＝ x
  paths =  centre-cell

  paths⁻ : ⦃ A-c : is-contr⁻ A ⦄ (x : A) → x ＝ centre
  paths⁻ = centre-cell


is-prop : {ℓ : Level} (A : Type ℓ) → Type ℓ
is-prop A = Thin (𝑩 A) Strict lzero lzero
{-# DISPLAY Thin {_} {_} {_} (𝑩 A) Strict _ _ = is-prop A #-}


HLevel : Type₀
HLevel = ℕ

-- TODO generalize to structures on hom types
_on-paths-of_ : {ℓ ℓ′ : Level} (S : Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ l⊔ ℓ′)
S on-paths-of A = (a a′ : A) → S (a ＝ a′)

is-of-hlevel : {ℓ : Level} → HLevel → Type ℓ → Type ℓ
is-of-hlevel 0 A = is-contr A
is-of-hlevel 1 A = is-prop  A
is-of-hlevel (suc (suc h)) A = is-of-hlevel (suc h) on-paths-of A

is-set is-groupoid is-2-groupoid : {ℓ : Level} → Type ℓ → Type ℓ
is-set = is-of-hlevel 2
is-groupoid = is-of-hlevel 3
is-2-groupoid = is-of-hlevel 4


-- Essential properties of `is-prop` and `is-contr`

-- is-prop→pathᴾ : {ℓ : Level} {B : I → Type ℓ}
--                 (h : (i : I) → is-prop (B i))
--               → (b₀ : B i0) (b₁ : B i1)
--               → Pathᴾ B b₀ b₁
-- is-prop→pathᴾ h b₀ b₁ = to-pathᴾ (h _ _ _)

is-contr→is-prop : {ℓ : Level} {A : Type ℓ} → is-contr A → is-prop A
is-contr→is-prop {A} A-c .thin-cell x y i = hcomp (∂ i) sys
  module is-contr→is-prop-sys where
  sys : (j : I) → Partial (∂ i ∨ ~ j) A
  sys j (i = i0) = paths ⦃ A-c ⦄ x j
  sys j (i = i1) = paths ⦃ A-c ⦄ y j
  sys j (j = i0) = centre ⦃ A-c ⦄
{-# DISPLAY hcomp _ (is-contr→is-prop-sys.sys {ℓ} {A} A-c x y i) = is-contr→is-prop {ℓ} {A} A-c x y i #-}

contractible-if-inhabited : {ℓ : Level} {A : Type ℓ} → (A → is-contr A) → is-prop A
contractible-if-inhabited cont .thin-cell x y = is-contr→is-prop (cont x) .thin-cell x y

is-prop→is-set : {ℓ : Level} {A : Type ℓ} → is-prop A → is-set A
is-prop→is-set {A} h a b .thin-cell p q j i = hcomp (∂ i ∨ ∂ j) sys
  module is-prop→is-set-sys where
  sys : (k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) A
  sys k (i = i0) = h .thin-cell a a k
  sys k (i = i1) = h .thin-cell a b k
  sys k (j = i0) = h .thin-cell a (p i) k
  sys k (j = i1) = h .thin-cell a (q i) k
  sys k (k = i0) = a
{-# DISPLAY hcomp _ (is-prop→is-set-sys.sys {ℓ} {A} h a b p q j i) = is-prop→is-set {ℓ} {A} h a b p q i j #-}

is-of-hlevel-suc : {ℓ : Level} {A : Type ℓ} (h : HLevel) → is-of-hlevel h A → is-of-hlevel (suc h) A
is-of-hlevel-suc 0 x = is-contr→is-prop x
is-of-hlevel-suc 1 x = is-prop→is-set x
is-of-hlevel-suc (suc (suc h)) p x y = is-of-hlevel-suc (suc h) (p x y)

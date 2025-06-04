{-# OPTIONS --safe #-}
module Foundations.HLevel.Base where

open import Prim.Data.Nat
open import Prim.Type

open import Notation.Displayed.Total

open import Foundations.Path.Groupoid.Base
open import Foundations.Singleton

centre : ∀{ℓ} {A : Type ℓ} → is-contr A → A
centre = carrier

paths : ∀{ℓ} {A : Type ℓ} (A-c : is-contr A) (x : A) → centre A-c ＝ x
paths A-c x = A-c .structured x

-- TODO can you state it as a displayed structure?
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

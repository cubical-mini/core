{-# OPTIONS --safe #-}
module Foundations.HLevel.Base where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete
open import Foundations.Quiver.Path

HLevel : Type₀
HLevel = ℕ

-- TODO generalize to structures on hom types or use display?
_on-paths-of_ : ∀{ℓ ℓ′} (S : Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ ⊔ ℓ′)
S on-paths-of A = (a a′ : A) → S (a ＝ a′)

is-contr=⁻ is-contr=⁺ is-prop= : ∀{ℓa} (A : Type ℓa) → Type ℓa
is-contr=⁻ A = is-contr⁻ A discrete-path-object
is-contr=⁺ A = is-contr⁺ A discrete-path-object
is-prop=   A = is-prop A discrete-path-object
{-# NOINLINE is-contr=⁻ #-}
{-# NOINLINE is-contr=⁺ #-}
{-# NOINLINE is-prop= #-}

is-of-hlevel : ∀{ℓ} → HLevel → Type ℓ → Type ℓ
is-of-hlevel 0 A = is-contr⁻ A discrete-path-object
is-of-hlevel 1 A = is-prop A discrete-path-object
is-of-hlevel (suc (suc h)) A = is-of-hlevel (suc h) on-paths-of A

is-set is-groupoid is-2-groupoid : ∀{ℓ} → Type ℓ → Type ℓ
is-set = is-of-hlevel 2
is-groupoid = is-of-hlevel 3
is-2-groupoid = is-of-hlevel 4

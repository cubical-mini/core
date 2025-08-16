{-# OPTIONS --safe #-}
module Foundations.Cubical.HLevel.Base where

open import Prim.Kan

open import Foundations.Base

HLevel : Type₀
HLevel = ℕ

-- TODO generalize to structures on hom types or use display?
_on-paths-of_ : ∀{ℓ ℓ′} (S : Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ ⊔ ℓ′)
S on-paths-of A = (a a′ : A) → S (a ＝ a′)

is-central : ∀{ℓ} {A : Type ℓ} → A → Type ℓ
is-central {A} c = (x : A) → c ＝ x ; {-# NOINLINE is-central #-}

is-contr is-prop is-set is-groupoid : ∀{ℓ} → Type ℓ → Type ℓ
is-contr    A = Σₜ A is-central ; {-# NOINLINE is-contr #-}
is-prop     A = (x y : A) → x ＝ y ; {-# NOINLINE is-prop #-}
is-set      A = (x y : A) (p q : x ＝ y) → p ＝ q ; {-# NOINLINE is-set #-}
is-groupoid A = (x y : A) (p q : x ＝ y) (r s : p ＝ q) → r ＝ s ; {-# NOINLINE is-groupoid #-}

is-of-hlevel : ∀{ℓ} → HLevel → Type ℓ → Type ℓ
is-of-hlevel 0       A = is-contr A
is-of-hlevel (suc h) A = is-of-hlevel h on-paths-of A
{-# NOINLINE is-of-hlevel #-}


-- Automation

record H-Level {ℓ} (n : ℕ) (T : Type ℓ) : Type ℓ where
  no-eta-equality
  constructor hlevel-instance
  field has-hlevel : is-of-hlevel n T
{-# INLINE hlevel-instance #-}

hlevel : ∀{ℓ} {A : Type ℓ} (n : HLevel) ⦃ hl : H-Level n A ⦄ → is-of-hlevel n A
hlevel n ⦃ hl ⦄ = hl .H-Level.has-hlevel

hlevel! : ∀{ℓ} {A : Type ℓ} ⦃ hl : H-Level 0 A ⦄ → A
hlevel! ⦃ hl ⦄ = hlevel 0 .fst

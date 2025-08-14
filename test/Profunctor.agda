{-# OPTIONS --safe #-}
module Profunctor where

open import Foundations.Base
open import Foundations.Codiscrete
open import Foundations.Discrete as Discrete
open import Foundations.Dual
open import Foundations.Lens.Pull
open import Foundations.Lens.Push

open import Notation.Refl
open import Notation.Sym

data _≤_ : ℕ → ℕ → Type where
  z≤ : ∀{n} → 0 ≤ n
  s≤ : ∀{m n} → m ≤ n → suc m ≤ suc n

≤-refl : ∀ n → n ≤ n
≤-refl 0 = z≤
≤-refl (suc n) = s≤ (≤-refl n)

≤-double-trans : ∀ {m n k l} → m ≤ n → k ≤ l → n ≤ k → m ≤ l
≤-double-trans z≤ _ _ = z≤
≤-double-trans (s≤ p) (s≤ q) (s≤ r) = s≤ (≤-double-trans p q r)

≤-trans : ∀ {m n k} → m ≤ n → n ≤ k → m ≤ k
≤-trans z≤     _      = z≤
≤-trans (s≤ p) (s≤ q) = s≤ (≤-trans p q)


LTE : HQuiver-onω 0 (λ _ → ℕ) λ _ _ → lzero
LTE .Quiver-onω.Het = _≤_

instance
  ≤-Refl : Refl LTE
  ≤-Refl .refl = ≤-refl _

  ≤-Push : {m : ℕ} → HPush LTE 0 λ n → Codisc (m ≤ n)
  ≤-Push ._▷_ = ≤-trans
  ≤-Push .push-refl = tt

  ≤-Pull : {n : ℕ} → HPull LTE 0 λ m → Codisc (m ≤ n)
  ≤-Pull ._◁_ = ≤-trans
  ≤-Pull .pull-refl = tt

data Fin : ℕ → Type where
  fzero : ∀{n} → Fin (suc n)
  fsuc  : ∀{n} → Fin n → Fin (suc n)

Fin-Funs-on : HQuiver-onω 0 (λ _ → ℕ) λ _ _ → lzero
Fin-Funs-on .Quiver-onω.Het m n = Fin m → Fin n

fin-cast-≤ : ∀{m n} → m ≤ n → Fin m → Fin n
fin-cast-≤ (s≤ _) fzero = fzero
fin-cast-≤ (s≤ p) (fsuc k) = fsuc (fin-cast-≤ p k)

fin-cast-good : ∀{m} (k : Fin m) → k ＝ fin-cast-≤ refl k
fin-cast-good {suc m} fzero = refl
fin-cast-good {suc m} (fsuc k) i = fsuc (fin-cast-good k i)

instance
  Fin-Push : HPush LTE 0 (λ n → Disc (Fin n))
  Fin-Push ._▷_ k p = fin-cast-≤ p k
  Fin-Push .push-refl = sym (fin-cast-good _)

test : Fin 2 → Fin 3
test k = k ▷ s≤ (s≤ z≤)

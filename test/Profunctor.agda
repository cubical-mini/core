{-# OPTIONS --safe #-}
module Profunctor where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Codiscrete
open import Foundations.Quiver.Discrete as Discrete
open import Foundations.Quiver.Dual

open import Notation.Profunctor
open import Notation.Push
open import Notation.Refl

data _≤_ : ℕ → ℕ → Type where
  z≤ : ∀{n} → 0 ≤ n
  s≤ : ∀{m n} → m ≤ n → suc m ≤ suc n

≤-refl : ∀ n → n ≤ n
≤-refl 0 = z≤
≤-refl (suc n) = s≤ (≤-refl n)

≤-double-trans : ∀ {m n k l} → m ≤ n → k ≤ l → n ≤ k → m ≤ l
≤-double-trans z≤ _ _ = z≤
≤-double-trans (s≤ p) (s≤ q) (s≤ r) = s≤ (≤-double-trans p q r)

LTE : HQuiver-onω 0 (λ _ → ℕ) λ _ _ → lzero
LTE .Quiver-onω.Het = _≤_

instance
  ≤-Refl : Refl LTE
  ≤-Refl .refl = ≤-refl _

  ≤-Profunctor : HProfunctor LTE LTE 0 (λ x y → Codisc (x ≤ y))
  ≤-Profunctor .dimap = ≤-double-trans
  ≤-Profunctor .dimap-refl = tt

data Fin : ℕ → Type where
  fzero : ∀{n} → Fin (suc n)
  fsuc  : ∀{n} → Fin n → Fin (suc n)

Fin-Funs-on : HQuiver-onω 0 (λ _ → ℕ) λ _ _ → lzero
Fin-Funs-on .Quiver-onω.Het m n = Fin m → Fin n

fin-cast-≤ : ∀{m n} → m ≤ n → Fin m → Fin n
fin-cast-≤ (s≤ _) fzero = fzero
fin-cast-≤ (s≤ p) (fsuc k) = fsuc (fin-cast-≤ p k)

open Discrete.Groupoid
fin-cast-good : ∀{m} (k : Fin m) → k ＝ fin-cast-≤ refl k
fin-cast-good {suc m} fzero = refl
fin-cast-good {suc m} (fsuc k) i = fsuc (fin-cast-good k i)

instance
  Fin-Push : HPush LTE 0 (λ n → Disc (Fin n))
  Fin-Push .push = fin-cast-≤
  Fin-Push .push-refl = fin-cast-good _

  Fin-Profunctor : HProfunctor LTE LTE 0 (λ m n → Disc (Fin m → Fin n))
  Fin-Profunctor .dimap p q f kw = q <$> f (p <$> kw)
  Fin-Profunctor .dimap-refl {u} i k = fin-cast-good (u (fin-cast-good k i)) i

test : Fin 2 → Fin 3
test = s≤ (s≤ z≤) ◁ fsuc ▷ s≤ (s≤ (s≤ z≤))

{-# OPTIONS --safe #-}
module Profunctor where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete
open import Foundations.Quiver.Dual

open import Notation.Lens.Covariant
open import Notation.Lens.Divariant
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
  ≤-Profunctor : HProfunctorω LTE LTE LTE
  ≤-Profunctor .dimap = ≤-double-trans

  ≤-Refl : Reflω LTE
  ≤-Refl .refl = ≤-refl _

data Fin : ℕ → Type where
  fzero : ∀{n} → Fin (suc n)
  fsuc  : ∀{n} → Fin n → Fin (suc n)

Fin-Funs-on : HQuiver-onω 0 (λ _ → ℕ) λ _ _ → lzero
Fin-Funs-on .Quiver-onω.Het m n = Fin m → Fin n

fin-cast-≤ : ∀{m n} → m ≤ n → Fin m → Fin n
fin-cast-≤ (s≤ _) fzero = fzero
fin-cast-≤ (s≤ p) (fsuc k) = fsuc (fin-cast-≤ p k)

instance
  Fin-Push : HPushω LTE Fin
  Fin-Push .push = fin-cast-≤

  Fin-Profunctor : HProfunctorω LTE LTE Fin-Funs-on
  Fin-Profunctor .dimap p q f kw = q <$> f (p <$> kw)

test : Fin 2 → Fin 3
test = s≤ (s≤ z≤) ∙∙ fsuc ∙∙ s≤ (s≤ (s≤ z≤))

{-# OPTIONS --safe #-}
module Nat where

open import Prim.Data.Empty as ⊥
open import Prim.Data.Nat
open import Prim.Data.Unit
open import Prim.Type

open import Notation.Base
open import Notation.Displayed.Base
open import Notation.Displayed.Push
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Symmetry

open import Foundations.Path.Groupoid
open import Foundations.Path.Transport

data _≤_ : ℕ → ℕ → Type where
  instance
    z≤ : ∀ {n} → 0 ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

data Fin : ℕ → Type where
  fzero : ∀{n} →         Fin (suc n)
  fsuc  : ∀{n} → Fin n → Fin (suc n)


Nats : Small-quiver-on ℕ lzero
Nats .Small-quiver-on.Hom = _≤_

≤-refl : ∀{n} → n ≤ n
≤-refl {0}     = z≤
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀{m n k} → m ≤ n → n ≤ k → m ≤ k
≤-trans z≤      _       = z≤
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

suc-inj : ∀{m n} → suc m ＝ suc n → m ＝ n
suc-inj p = ap pred p where
  pred : ℕ → ℕ
  pred zero = zero
  pred (suc m) = m

open Path-gpd0
s≠z : ∀ {m} → suc m ＝ 0 → ⊥
s≠z p = subst discrim (sym p) tt where
  discrim : ℕ → Type
  discrim zero    = ⊤
  discrim (suc _) = ⊥

fin-≤-push : ∀{m n} → m ≤ n → Fin m → Fin n
fin-≤-push (s≤s p) fzero = fzero
fin-≤-push (s≤s p) (fsuc k) = fsuc (fin-≤-push p k)

fin-=-push : ∀ {m n} → m ＝ n → Fin m → Fin n
fin-=-push {suc m} {0}     p k        = ⊥.rec (s≠z p)
fin-=-push {suc m} {suc n} _ fzero    = fzero
fin-=-push {suc m} {suc n} p (fsuc k) = fsuc (fin-=-push (suc-inj p) k)

fin-=-push-id : ∀ {n} (k : Fin n) → fin-=-push refl k ＝ k
fin-=-push-id {(n)} fzero = refl
fin-=-push-id {(n)} (fsuc k) = ap fsuc (fin-=-push-id k)

open Path-gpd
instance
  ≤-Refl : Refl (Enlarge Nats) lzero
  ≤-Refl .refl = ≤-refl

  ≤-Comp : Comp (Enlarge Nats) lzero lzero lzero
  ≤-Comp ._∙_ = ≤-trans

  Fin-≤-Push : Push (Enlarge Nats) Fin lzero lzero
  Fin-≤-Push .push = fin-≤-push

  Fin-=-Push : Pushω (Pathsω ℕ) Fin
  Fin-=-Push .push = fin-=-push

  Fin-=-Push0 : Push (Pathsω ℕ) Fin lzero lzero
  Fin-=-Push0 .push = fin-=-push
  {-# OVERLAPPING Fin-=-Push0 #-}

  Fin-=-Push-Id : Push-Id (Pathsω ℕ) Fin {λ _ _ → lzero} (λ t → Pathsω (Fin t)) lzero
  Fin-=-Push-Id .push-id = fin-=-push-id _

module const-index where private
  -- sucks : ∀ (k : Fin 2) → subst Fin refl k ＝ k
  -- sucks k = {!!} -- Nat.transpFin

  real : ∀ (k : Fin 2) → push reflₚ k ＝ k
  real k = push-id

module const-val where private
  -- sucks : ∀ {n} (k : Fin (suc n)) → subst Fin refl k ＝ k
  -- sucks k = {!!} -- Nat.transpFin

  real : ∀ {n} (k : Fin (suc n)) → push reflₚ k ＝ k
  real k = push-id

module const where private
  k : Fin 2
  k = fsuc fzero

  -- sucks : subst Fin refl k ＝ k
  -- sucks = {!!} -- Nat.transpX-Fin

  real : push reflₚ k ＝ k
  real = refl -- fire

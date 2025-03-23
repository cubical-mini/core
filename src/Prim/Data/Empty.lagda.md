```agda
{-# OPTIONS --safe #-}

module Prim.Data.Empty where

open import Prim.Base.Type

infixl 6 ¬_ ¬¬_ ¬¬¬_

data ⊥ : Type where

ind-⊥ : ∀ {ℓ} (P : ⊥ → Type ℓ) (e : ⊥) → P e
ind-⊥ P ()

rec-⊥ : ∀ {ℓ} {A : Type ℓ} → ⊥ → A
rec-⊥ {A = A} = ind-⊥ (λ _ → A)

syntax rec-⊥ = absurd

¬_ ¬¬_ ¬¬¬_ is-empty : ∀ {ℓ} → Type ℓ → Type ℓ
¬ A = A → ⊥
¬¬ A = ¬ (¬ A)
¬¬¬ A = ¬ (¬ (¬ A))
is-empty = ¬_

contra : ∀ {ℓ ℓ'} {P : Type ℓ} {Q : Type ℓ'} → (P → Q) → ¬ Q → ¬ P
contra pq nq p = nq (pq p)

```

For the level-polymorphic version of Empty, we'll use TypeTopology's
notation and implement it using Lift.

```

𝟘 : ∀ {ℓ} → Type ℓ
𝟘 {ℓ} = Lift ℓ ⊥

module _ where
  ind-𝟘 : ∀ {ℓ ℓ'} (P : 𝟘 {ℓ} → Type ℓ') (e : 𝟘 {ℓ}) → P e
  ind-𝟘 P e = rec-⊥ (lower e) 

  rec-𝟘 : ∀ {ℓ ℓ'} {A : Type ℓ} → 𝟘 {ℓ'} → A
  rec-𝟘 {A = A} = ind-𝟘 (λ _ → A)

```

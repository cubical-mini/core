```agda

{-# OPTIONS --safe #-}

module Prim.Data.Unit where

open import Prim.Base.Type using ( Type; Lift; lift )
open import Prim.Base.Interval using ( _＝_ )
open import Agda.Builtin.Unit public

module _ {ℓ} (P : ⊤ → Type ℓ) (p : P tt) where
  ind-⊤ : (x : ⊤) → P x
  ind-⊤ ._ = p

  indβ-⊤ : ind-⊤ tt ＝ p
  indβ-⊤ i = p

```

Level polymorphic unit, using Lift

```

𝟙 : ∀ {ℓ} → Type ℓ
𝟙 {ℓ} = Lift ℓ ⊤

ttℓ : ∀ {ℓ} → 𝟙 {ℓ}
ttℓ = lift tt

module _ {ℓ ℓ'} (P : 𝟙 {ℓ} → Type ℓ') (p : P ttℓ) where
  ind-𝟙 : (x : 𝟙) → P x
  ind-𝟙 ._ = p

  indβ-𝟙 : ind-𝟙 ttℓ ＝ p
  indβ-𝟙 i = p

instance
  𝟙-tt : ∀ {ℓ} → 𝟙 {ℓ}
  𝟙-tt = lift tt

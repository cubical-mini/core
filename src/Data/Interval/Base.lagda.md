The internalized interval as a higher inductive type

```agda

module Data.Interval.Base where

open import Prim.Base

open import Lib.HLevel.Base

data 𝕀 : Type where
  𝟎 : 𝕀
  𝟏 : 𝕀
  ipath : 𝟎 ＝ 𝟏

ind-𝕀 : ∀ {ℓ} (P : 𝕀 → Type ℓ) (b₀ : P 𝟎) (b₁ : P 𝟏)
      → PathP (λ i → P (ipath i)) b₀ b₁
      → (i : 𝕀) → P i
ind-𝕀 P b₀ b₁ bₚ 𝟎 = b₀
ind-𝕀 P b₀ b₁ bₚ 𝟏 = b₁
ind-𝕀 P b₀ b₁ bₚ (ipath i) = bₚ i

rec-𝕀 : ∀ {ℓ} {A : Type ℓ} → (x y : A) → x ＝ y → (i : 𝕀) → A
rec-𝕀 x y p 𝟎 = x
rec-𝕀 x y p 𝟏 = y
rec-𝕀 x y p (ipath i) = p i

_⊗_ : 𝕀 → 𝕀 → 𝕀
𝟎 ⊗ j = 𝟎
𝟏 ⊗ j = j
ipath i ⊗ 𝟎 = 𝟎
ipath i ⊗ 𝟏 = ipath i
ipath i ⊗ ipath j = ipath (i ∧ j)

_⊕_ : 𝕀 → 𝕀 → 𝕀
𝟎 ⊕ j = j
𝟏 ⊕ j = 𝟏
ipath i ⊕ 𝟎 = ipath i
ipath i ⊕ 𝟏 = 𝟏
ipath i ⊕ ipath j = ipath (i ∨ j)

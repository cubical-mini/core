```agda
{-# OPTIONS --safe #-}

module Prim.Base.Type where

open import Agda.Primitive public
  using ( SSet
        ; SSetω
        ; LevelUniv
        ; Level )
  renaming ( Prop  to DIProp
           ; Set   to Type
           ; Setω  to Typeω
           ; _⊔_ to infixl 6 _⊔_
           ; lsuc to infixr 7 _₊
           ; lzero to 0ℓ )

1ℓ : Level
1ℓ = 0ℓ ₊

Type₊ : ∀ ℓ → Type (ℓ ₊ ₊)
Type₊ ℓ = Type (ℓ ₊)

level-of : ∀ {ℓ} {A : Type ℓ} → A → Level
level-of {ℓ} _ = ℓ

record Lift {u} ℓ (A : Type u) : Type (u ⊔ ℓ) where
  constructor lift
  field
    lower : A

open Lift public

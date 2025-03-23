```agda

{-# OPTIONS --safe #-}

module Prim.Data.Sum where

open import Prim.Base.Type

infixr 1 _⊎_

data _⊎_ {u v} (A : Type u) (B : Type v) : Type (u ⊔ v) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

ind-⊎ : ∀ {u v w} {A : Type u} {B : Type v} {C : A ⊎ B → Type w}
     → (f : (a : A) → C (inl a)) (g : (b : B) → C (inr b))
     → (s : A ⊎ B) → C s
ind-⊎ f _ (inl x) = f x
ind-⊎ _ g (inr x) = g x
{-# INLINE ind-⊎ #-}

rec-⊎ : ∀ {u v w} {A : Type u} {B : Type v} {R : Type w}
    → (A → R) → (B → R) → A ⊎ B → R
rec-⊎ = ind-⊎
{-# INLINE rec-⊎ #-}

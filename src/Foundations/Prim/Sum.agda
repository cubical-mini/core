{-# OPTIONS --safe #-}
module Foundations.Prim.Sum where

open import Foundations.Prim.Type

infixr 70 _⊎_
data _⊎_ {ℓa ℓb} (A : Type ℓa) (B : Type ℓb) : Type (ℓa l⊔ ℓb) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

elim : {ℓa ℓb : Level} {A : Type ℓa} {B : Type ℓb}
       {ℓ : Level} {C : A ⊎ B → Type ℓ}
       (f : (a : A) → C (inl a)) (g : (b : B) → C (inr b))
     → (s : A ⊎ B) → C s
elim f _ (inl x) = f x
elim _ g (inr x) = g x

rec : {ℓa ℓb : Level} {A : Type ℓa} {B : Type ℓb}
      {ℓ : Level} {R : Type ℓ}
    → (A → R) → (B → R) → A ⊎ B → R
rec = elim

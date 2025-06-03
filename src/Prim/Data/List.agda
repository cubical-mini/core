{-# OPTIONS --safe #-}
module Prim.Data.List where

open import Prim.Type

open import Agda.Builtin.List public

elim
  : {ℓa ℓp : Level} {A : Type ℓa} (P : List A → Type ℓp)
  → P []
  → (∀ x xs → P xs → P (x ∷ xs))
  → ∀ xs → P xs
elim P p[] p∷ []       = p[]
elim P p[] p∷ (x ∷ xs) = p∷ x xs (elim P p[] p∷ xs)

-- aka fold-r
rec : {ℓa ℓb : Level} {A : Type ℓa} {B : Type ℓb} → B → (A → B → B) → List A → B
rec x _ []       = x
rec x f (a ∷ as) = f a (rec x f as)

-- rec {B} b f = elim (λ _ → B) b (λ x _ → f x)

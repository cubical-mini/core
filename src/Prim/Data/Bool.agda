{-# OPTIONS --safe #-}
module Prim.Data.Bool where

open import Prim.Type

open import Agda.Builtin.Bool public

elim : {ℓ : Level} {P : Bool → Type ℓ} (t : P true) (f : P false) (b : Bool) → P b
elim _ f false = f
elim t _ true  = t

rec : {ℓ : Level} {A : Type ℓ} → A → A → Bool → A
rec = elim

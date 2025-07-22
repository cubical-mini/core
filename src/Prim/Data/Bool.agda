{-# OPTIONS --safe #-}
module Prim.Data.Bool where

open import Prim.Type
open import Prim.Data.Empty using (⊥)
open import Prim.Data.Unit

open import Agda.Builtin.Bool public

elim : ∀{ℓ} {P : Bool → Type ℓ} (t : P true) (f : P false) (b : Bool) → P b
elim _ f false = f
elim t _ true  = t

rec : ∀{ℓ} {A : Type ℓ} → A → A → Bool → A
rec = elim

infixr 60 _implies_
_implies_ : Bool → Bool → Bool
true  implies false = false
false implies _     = true
true  implies true  = true

infix 0 if_then_else_
if_then_else_ : ∀{ℓ} {A : Type ℓ} → Bool → A → A → A
if b then tr else fa = rec tr fa b
{-# NOINLINE if_then_else_ #-}

record So (b : Bool) : Type where
  field is-so : if b then ⊤ else ⊥

pattern oh = record { is-so = tt }

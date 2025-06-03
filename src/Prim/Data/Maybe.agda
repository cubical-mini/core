{-# OPTIONS --safe #-}
module Prim.Data.Maybe where

open import Prim.Type

open import Agda.Builtin.Maybe public

elim : {ℓa ℓb : Level} {A : Type ℓa} (B : Maybe A → Type ℓb)
       (b : B nothing)
       (f : (a : A) → B (just a))
     → (mx : Maybe A) → B mx
elim B b f nothing  = b
elim B n f (just x) = f x

rec : {ℓa ℓb : Level} {A : Type ℓa} {B : Type ℓb} → B → (A → B) → Maybe A → B
rec b f (just x) = f x
rec b _ nothing  = b
-- rec = elim _

{-# OPTIONS --safe #-}
module Prim.Data.Nat where

open import Prim.Type

open import Agda.Builtin.Nat public
  using
    ( zero
    ; suc
    ; _+_
    ; _==_
    ; div-helper
    ; mod-helper )
  renaming
    ( Nat to ℕ
    ; _-_ to _∸_
    ; _*_ to _·_
    ; _<_ to infix 30 _<?_ )

elim : {ℓ : Level} (P : ℕ → Type ℓ)
     → P 0
     → ({n : ℕ} → P n → P (suc n))
     → (n : ℕ) → P n
elim P pz ps zero    = pz
elim P pz ps (suc n) = elim (λ n → P (suc n)) (ps pz) ps n

rec : {ℓ : Level} {A : Type ℓ} → A → (A → A) → ℕ → A
rec z s = elim _ z s

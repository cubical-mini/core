{-# OPTIONS --safe #-}
module Notation.Base where

open import Prim.Data.Nat public
open import Prim.Data.Sigma public
open import Prim.Data.Unit public
open import Prim.Type public

-- vector of levels
Levels : ℕ → Type
Levels zero = ⊤
Levels (suc n) = Σ Level λ _ →  Levels n

-- object level adjustment
ℓ-sig : ℕ → Type
ℓ-sig n = Levels n → Level

-- arrow level adjustment
ℓ-sig² : ℕ → Type
ℓ-sig² n = Levels n → Levels n → Level

-- reflexive quiver of arbitrary size
record Quiverω (n : ℕ) (ℓ-ob : ℓ-sig n) (ℓ-hom : ℓ-sig² n) : Typeω where
  constructor mk-quiverω
  no-eta-equality
  field
    Ob   : (ls : Levels n) → Type (ℓ-ob ls)
    Hom  : {lxs lys : Levels n} → Ob lxs → Ob lys → Type (ℓ-hom lxs lys)
{-# INLINE mk-quiverω #-}


-- displayed reflexive quiver of arbitrary size
module _ {n : ℕ} {ℓ-obω : ℓ-sig n} {ℓ-homω : ℓ-sig² n} (C : Quiverω n ℓ-obω ℓ-homω) (open Quiverω C) where
  record Quiverωᵈ (m : ℕ) (ℓ-obωᵈ : Levels n → ℓ-sig m) (ℓ-homωᵈ : Levels n → Levels n → ℓ-sig² m) : Typeω where
    constructor mk-quiverωᵈ
    no-eta-equality
    field
      Ob[_]  : {ls : Levels n} (x : Ob ls) (lsᵈ : Levels m) → Type (ℓ-obωᵈ ls lsᵈ)
      Hom[_] : {lxs lys : Levels n} {x : Ob lxs} {y : Ob lys} (f : Hom x y)
               {lxsᵈ lysᵈ : Levels m} (x′ : Ob[ x ] lxsᵈ) (y′ : Ob[ y ] lysᵈ) → Type (ℓ-homωᵈ lxs lys lxsᵈ lysᵈ)
  {-# INLINE mk-quiverωᵈ #-}

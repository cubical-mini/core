{-# OPTIONS --safe #-}
module Notation.Wide where

open import Notation.Base
open import Notation.Total

module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m : ℕ} {ℓ-obᵈ : Levels n → ℓ-sig m} {ℓ-homᵈ : Levels n → Levels n → ℓ-sig² m}
  (D : Quiverωᵈ C m ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D)
  (lsᵈ : Levels m) (t : {ls : Levels n} {x : Ob ls} → Ob[ x ] lsᵈ)
  where

  Wide : Quiverω n ℓ-ob _
  Wide .Quiverω.Ob = Ob
  Wide .Quiverω.Hom x y = ΣHom C D {x = x} {y = y} t t

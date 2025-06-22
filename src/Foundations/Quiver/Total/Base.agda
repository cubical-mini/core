{-# OPTIONS --safe #-}
module Foundations.Quiver.Total.Base where

open import Foundations.Quiver.Base

ℓ-split : ∀ n {m} → Levels (n + m) → Levels n × Levels m
ℓ-split 0 ls = tt , ls
ℓ-split (suc n) (l , ls) = let left , right = ℓ-split n ls in (l , left) , right

module _ {n : ℕ} {ℓ-ob : ℓ-sig n}
  (Ob : (ls : Levels n) → Type (ℓ-ob ls))
  {m : ℕ} {ℓ-obᵈ : Levels n → ℓ-sig m}
  (Ob[_] : {ls : Levels n} (x : Ob ls) (lsᵈ : Levels m) → Type (ℓ-obᵈ ls lsᵈ))
  where

  ΣOb : (ls : Levels n) (lsᵈ : Levels m) → Type (ℓ-obᵈ ls lsᵈ ⊔ ℓ-ob ls)
  ΣOb ls lsᵈ = Σ (Ob ls) λ x → Ob[ x ] lsᵈ

module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C)
  {m : ℕ} {ℓ-obᵈ : Levels n → ℓ-sig m} {ℓ-homᵈ : Levels n → Levels n → ℓ-sig² m}
  (D : Quiverωᵈ C m ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D)
  {lxs lys : Levels n} {x : Ob lxs} {y : Ob lys}
  where

  -- saturated application of total arrow signature
  infixr 40 _,⃗_
  record ΣHom {lxsᵈ lysᵈ} (x′ : Ob[ x ] lxsᵈ) (y′ : Ob[ y ] lysᵈ) : Type (ℓ-hom lxs lys ⊔ ℓ-homᵈ lxs lys lxsᵈ lysᵈ) where
    constructor _,⃗_
    field
      hom       : Hom x y
      preserves : Hom[ hom ] x′ y′
  open ΣHom public


module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m : ℕ} {ℓ-obᵈ : Levels n → ℓ-sig m} {ℓ-homᵈ : Levels n → Levels n → ℓ-sig² m}
  (D : Quiverωᵈ C m ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D) where

  -- total quiver of arbitrary size
  ∫ : Quiverω (n + m) _ _
  ∫ .Quiverω.Ob ∫ls =
    let ls , lsᵈ = ℓ-split n ∫ls
    in ΣOb Ob Ob[_] ls lsᵈ
  ∫ .Quiverω.Hom (x , x′) (y , y′) = ΣHom C D x′ y′

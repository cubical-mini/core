{-# OPTIONS --safe #-}
module Foundations.Quiver.Total.Base where

open import Foundations.Quiver.Base

ℓ-split : ∀ n {m} → Levels (n + m) → Levels n × Levels m
ℓ-split 0 ls = tt , ls
ℓ-split (suc n) (l , ls) = let left , right = ℓ-split n ls in (l , left) , right

module _ {n ℓ-ob} (Ob : ob-sig ℓ-ob) {m ℓ-obᵈ} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ) where

  ΣOb : (ls : Levels n) (lsᵈ : Levels m) → Type (ℓ-obᵈ ls lsᵈ ⊔ ℓ-ob ls)
  ΣOb ls lsᵈ = Σ (Ob ls) λ x → Ob[ x ] lsᵈ

module _ {n ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob} (C : Quiver-onω n Ob ℓ-hom) (open Quiver-onω C)
  {m ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ} (D : Quiver-onωᵈ Ob Hom m Ob[_] ℓ-homᵈ) (open Quiver-onωᵈ D)
  {lxs lys} {x : Ob lxs} {y : Ob lys} where

  infixr 40 _,⃗_
  record ΣHom {lxsᵈ lysᵈ} (x′ : Ob[ x ] lxsᵈ) (y′ : Ob[ y ] lysᵈ) : Type
    (ℓ-hom lxs lys ⊔ ℓ-homᵈ lxs lys lxsᵈ lysᵈ) where
    constructor _,⃗_
    field
      hom       : Hom x y
      preserves : Hom[ hom ] x′ y′
  open ΣHom public


module _ {n ℓ-ob ℓ-hom} {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m ℓ-obᵈ ℓ-homᵈ} (D : Quiverωᵈ C m ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D) where

  ∫ : Quiverω (n + m) _ _
  ∫ .Quiverω.Ob ∫ls =
    let ls , lsᵈ = ℓ-split n ∫ls
    in ΣOb Ob Ob[_] ls lsᵈ
  ∫ .has-quiver-onω .Quiver-onω.Hom (x , x′) (y , y′) =
    ΣHom (C .has-quiver-onω) (D .has-quiver-onωᵈ) x′ y′

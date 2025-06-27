{-# OPTIONS --safe #-}
module Foundations.Quiver.Total.Base where

open import Foundations.Quiver.Base

ℓ-split : ∀ m {m′} → Levels (m + m′) → Levels m ×ₜ Levels m′
ℓ-split 0 ls = tt , ls
ℓ-split (suc m) (l , ls) = let left , right = ℓ-split m ls in (l , left) , right

module _ {m ℓ-ob} (Ob : ob-sig ℓ-ob) {m′ ℓ-obᵈ} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ) where

  ΣOb : (ls : Levels m) (lsᵈ : Levels m′) → Type (ℓ-obᵈ ls lsᵈ ⊔ ℓ-ob ls)
  ΣOb ls lsᵈ = Σₜ (Ob ls) λ x → Ob[ x ] lsᵈ
  {-# NOINLINE ΣOb #-}

  ∫Ob : (∫ls : Levels (m + m′)) → Type _
  ∫Ob ∫ls = let ls , lsᵈ = ℓ-split m ∫ls in ΣOb ls lsᵈ


module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het} {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  (C : Quiver-onω m n Ob⁻ Ob⁺ ℓ-het) (open Quiver-onω C)
  {m′ n′ ℓ-obᵈ⁻ ℓ-obᵈ⁺ ℓ-hetᵈ} {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺}
  (D : Quiver-onωᵈ Ob⁻ Ob⁺ Het m′ n′ Ob[_]⁻ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D)
  {lxs lys} {x : Ob⁻ lxs} {y : Ob⁺ lys} where

  ΣHet : ∀ {lxsᵈ lysᵈ} (x′ : Ob[ x ]⁻ lxsᵈ) (y′ : Ob[ y ]⁺ lysᵈ)
       → Type (ℓ-het lxs lys ⊔ ℓ-hetᵈ lxs lys lxsᵈ lysᵈ)
  ΣHet x′ y′ = Σₜ (Het x y) λ f → Het[ f ] x′ y′
  {-# NOINLINE ΣHet #-}


module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het} {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  (C : Quiver-onω m n Ob⁻ Ob⁺ ℓ-het) (open Quiver-onω C)
  {m′ n′ ℓ-obᵈ⁻ ℓ-obᵈ⁺ ℓ-hetᵈ} {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺}
  (D : Quiver-onωᵈ Ob⁻ Ob⁺ Het m′ n′ Ob[_]⁻ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D) where

  ∫ : Quiver-onω (m + m′) (n + n′) (∫Ob Ob⁻ Ob[_]⁻) (∫Ob Ob⁺ Ob[_]⁺) _
  ∫ .Quiver-onω.Het (x , x′) (y , y′) = ΣHet C D x′ y′

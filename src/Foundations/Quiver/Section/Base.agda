{-# OPTIONS --safe #-}
module Foundations.Quiver.Section.Base where

open import Foundations.Quiver.Base

module _ {m ℓ-ob} (Ob : ob-sig ℓ-ob) {m′ ℓ-obᵈ} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ) where

  ΠOb : (Πls : Levels (m + m′)) → Type _
  ΠOb Πls = let ls , lsᵈ = ℓ-split m Πls in (x : Ob ls) → Ob[ x ] lsᵈ
  {-# NOINLINE ΠOb #-}


module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het} {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  (C : Quiver-onω m n Ob⁻ Ob⁺ ℓ-het) (open Quiver-onω C)
  {m′ n′ ℓ-obᵈ⁻ ℓ-obᵈ⁺ ℓ-hetᵈ} {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺}
  (D : Quiver-onωᵈ Ob⁻ Ob⁺ Het m′ n′ Ob[_]⁻ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D)
  {lxs lys} {x : Ob⁻ lxs} {y : Ob⁺ lys} where

  ΠHet : ∀ {lxsᵈ lysᵈ} (x′ : Ob[ x ]⁻ lxsᵈ) (y′ : Ob[ y ]⁺ lysᵈ)
       → Type (ℓ-het lxs lys ⊔ ℓ-hetᵈ lxs lys lxsᵈ lysᵈ)
  ΠHet x′ y′ = (f : Het x y) → Het[ f ] x′ y′
  {-# NOINLINE ΠHet #-}


module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het} {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  (C : Quiver-onω m n Ob⁻ Ob⁺ ℓ-het) (open Quiver-onω C)
  {m′ n′ ℓ-obᵈ⁻ ℓ-obᵈ⁺ ℓ-hetᵈ} {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺}
  (D : Quiver-onωᵈ Ob⁻ Ob⁺ Het m′ n′ Ob[_]⁻ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D) where

  Π : Quiver-onω (m + m′) (n + n′) (ΠOb Ob⁻ Ob[_]⁻) (ΠOb Ob⁺ Ob[_]⁺) _
  Π .Quiver-onω.Het f g = (x : Ob⁻ _) (y : Ob⁺ _) → ΠHet C D (f x) (g y)

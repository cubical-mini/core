module Foundations.Section where

open import Foundations.Base

module _ {m ℓ-ob} (Ob : ob-sig ℓ-ob) {m′ ℓ-obᵈ} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ) where

  ΠOb : (Πls : Levels (m + m′)) → Type _
  ΠOb Πls = let ls , lsᵈ = ℓ-split m Πls in (x : Ob ls) → Ob[ x ] lsᵈ
  {-# NOINLINE ΠOb #-}

  ∀Ob : (∀ls : Levels (m + m′)) → Type _
  ∀Ob ∀ls = let ls , lsᵈ = ℓ-split m ∀ls in {x : Ob ls} → Ob[ x ] lsᵈ
  {-# NOINLINE ∀Ob #-}


module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} (C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω C)
  {m′ ℓ-obᵈ⁻} {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻} {n′ ℓ-obᵈ⁺} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺}
  {ℓ-hetᵈ} (D : Quiver-onωᵈ C m′ Ob[_]⁻ n′ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D) where

  module _ {lxs lys} {x : Ob⁻ lxs} {y : Ob⁺ lys} where
    ΠHet : ∀ {lxsᵈ lysᵈ} (x′ : Ob[ x ]⁻ lxsᵈ) (y′ : Ob[ y ]⁺ lysᵈ)
         → Type (ℓ-het lxs lys ⊔ ℓ-hetᵈ lxs lys lxsᵈ lysᵈ)
    ΠHet x′ y′ = (f : Het x y) → Het[ f ] x′ y′
    {-# NOINLINE ΠHet #-}

  Π̫ : Quiver-onω (m + m′) (ΠOb Ob⁻ Ob[_]⁻) (n + n′) (ΠOb Ob⁺ Ob[_]⁺) _
  Π̫ .Quiver-onω.Het P Q = (x : Ob⁻ _) (y : Ob⁺ _) → ΠHet (P x) (Q y)

  ∀̫ : Quiver-onω (m + m′) (∀Ob Ob⁻ Ob[_]⁻) (n + n′) (∀Ob Ob⁺ Ob[_]⁺) _
  ∀̫ .Quiver-onω.Het P Q = {x : Ob⁻ _} {y : Ob⁺ _} → ΠHet (P {x}) (Q {y})


module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} {C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het} (open Quiver-onω C)
  {m′ ℓ-obᵈ⁻} {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻} {n′ ℓ-obᵈ⁺} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺}
  {ℓ-hetᵈ} (D : Quiver-onωᵈ C m′ Ob[_]⁻ n′ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D) where

  Π̫[_] = Π̫ C D
  ∀̫[_] = ∀̫ C D

module Foundations.Total.Base where

open import Foundations.Base

module _ {m ℓ-ob} (Ob : ob-sig ℓ-ob) {m′ ℓ-obᵈ} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ) where

  ΣOb : (Σls : Levels (m + m′)) → Type _
  ΣOb Σls = let ls , lsᵈ = ℓ-split m Σls in Σₜ (Ob ls) λ x → Ob[ x ] lsᵈ
  {-# NOINLINE ΣOb #-}


module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} (C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω C)
  {m′ ℓ-obᵈ⁻} {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻} {n′ ℓ-obᵈ⁺} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺}
  {ℓ-hetᵈ} (D : Quiver-onωᵈ C m′ Ob[_]⁻ n′ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D) where

  module _ {lxs lys} {x : Ob⁻ lxs} {y : Ob⁺ lys} where
    ΣHet : ∀ {lxsᵈ lysᵈ} (x′ : Ob[ x ]⁻ lxsᵈ) (y′ : Ob[ y ]⁺ lysᵈ)
         → Type (ℓ-het lxs lys ⊔ ℓ-hetᵈ lxs lys lxsᵈ lysᵈ)
    ΣHet x′ y′ = Σₜ (Het x y) λ f → Het[ f ] x′ y′
    {-# NOINLINE ΣHet #-}

  Σ̫ : Quiver-onω (m + m′) (ΣOb Ob⁻ Ob[_]⁻) (n + n′) (ΣOb Ob⁺ Ob[_]⁺) _
  Σ̫ .Quiver-onω.Het x y = ΣHet (x .snd) (y .snd)


module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} {C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het}
  {m′ ℓ-obᵈ⁻} {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻} {n′ ℓ-obᵈ⁺} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺}
  {ℓ-hetᵈ} (D : Quiver-onωᵈ C m′ Ob[_]⁻ n′ Ob[_]⁺ ℓ-hetᵈ) where

  Σ̫[_] = Σ̫ C D

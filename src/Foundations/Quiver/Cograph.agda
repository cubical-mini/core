{-# OPTIONS --safe #-}
module Foundations.Quiver.Cograph where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Interval.Base
open import Foundations.Quiver.Total.Base

module _ {m} {ℓ-ob : ℓ-sig 1 (m , _)} (Ob⁻ Ob⁺ : ob-sig ℓ-ob) where
  Choose : Bool → ob-sig ℓ-ob
  Choose false = Ob⁻
  Choose true  = Ob⁺

  private module 𝐼 = Quiver-onω 𝐼 renaming (Het to Hom)

  Arrows : ∀ ℓ-het → Typeω
  Arrows ℓ-het = HQuiver-onωᵈ 𝐼.Out 𝐼.Hom m Choose λ _ _ → ℓ-het

module _ {m} {ℓ-ob : ℓ-sig 1 (m , _)} {Ob⁻ Ob⁺ : ob-sig ℓ-ob} {ℓ-het} (D : Arrows Ob⁻ Ob⁺ ℓ-het) where
  Cograph : HQuiver-onω m _ _
  Cograph = Σ 𝐼 D

module _ {m ℓ-ob ℓ-het}
  {Ob⁻ : ob-sig ℓ-ob} (A : HQuiver-onω m Ob⁻ ℓ-het)
  (let module A = Quiver-onω A renaming (Het to Hom))
  {Ob⁺ : ob-sig ℓ-ob} (B : HQuiver-onω m Ob⁺ ℓ-het)
  (let module B = Quiver-onω B renaming (Het to Hom))
  (C : Quiver-onω m Ob⁻ m Ob⁺ ℓ-het) (let module C = Quiver-onω C) where

  Disp→ : Arrows Ob⁻ Ob⁺ ℓ-het
  Disp→ .Quiver-onωᵈ.Het[_] {x = false} {y = false} _ = A.Hom
  Disp→ .Quiver-onωᵈ.Het[_] {x = false} {y = true}  _ = C.Het
  Disp→ .Quiver-onωᵈ.Het[_] {x = true}  {y = true}  _ = B.Hom

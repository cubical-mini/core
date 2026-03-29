module Foundations.Collage where

open import Foundations.Base
open import Foundations.Interval.Base
open import Foundations.Total.Base

module _ {m} {ℓ-ob⁻ ℓ-ob⁺ : ℓ-sig 1 (m , _)} (Ob⁻ : ob-sig ℓ-ob⁻) (Ob⁺ : ob-sig ℓ-ob⁺) where
  Choose : Bool → ob-sig (λ ls → ℓ-ob⁻ ls ⊔ ℓ-ob⁺ ls)
  Choose false ls = Lift (ℓ-ob⁺ ls) (Ob⁻ ls)
  Choose true  ls = Lift (ℓ-ob⁻ ls) (Ob⁺ ls)

  Arrows : ∀ ℓ-het → Typeω
  Arrows ℓ-het = HQuiver-onωᵈ 𝐼 m Choose λ _ _ → ℓ-het

module _ {m} {ℓ-ob⁻ ℓ-ob⁺ : ℓ-sig 1 (m , _)} {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} (D : Arrows Ob⁻ Ob⁺ ℓ-het) where
  Cograph : HQuiver-onω m _ _
  Cograph = Σ̫[ D ]

module _ {m ℓ-ob⁻ ℓ-ob⁺ ℓ-hom⁻ ℓ-hom⁺}
  {Ob⁻ : ob-sig ℓ-ob⁻} (A : HQuiver-onω m Ob⁻ ℓ-hom⁻)
  (let module A = Quiver-onω A renaming (Het to Hom))
  {Ob⁺ : ob-sig ℓ-ob⁺} (B : HQuiver-onω m Ob⁺ ℓ-hom⁺)
  (let module B = Quiver-onω B renaming (Het to Hom))
  (C : Quiver-onω m Ob⁻ m Ob⁺ (λ lxs lys → ℓ-hom⁻ lxs lys ⊔ ℓ-hom⁺ lxs lys)) (let module C = Quiver-onω C) where

  Disp→ : Arrows Ob⁻ Ob⁺ (λ lxs lys → ℓ-hom⁻ lxs lys ⊔ ℓ-hom⁺ lxs lys)
  Disp→ .Quiver-onωᵈ.Het[_] {x = false} {y = false} _ {lxsᵈ} {lysᵈ} (lift x⁻) (lift y⁻) = Lift (ℓ-hom⁺ lxsᵈ lysᵈ) (A.Hom x⁻ y⁻)
  Disp→ .Quiver-onωᵈ.Het[_] {x = false} {y = true}  _ (lift x⁻) (lift y⁺) = C.Het x⁻ y⁺
  Disp→ .Quiver-onωᵈ.Het[_] {x = true}  {y = true}  _ {lxsᵈ} {lysᵈ} (lift x⁺) (lift y⁺) = Lift (ℓ-hom⁻ lxsᵈ lysᵈ) (B.Hom x⁺ y⁺)

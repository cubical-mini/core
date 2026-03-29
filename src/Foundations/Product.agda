module Foundations.Product where

open import Foundations.Base
open import Foundations.Const
open import Foundations.Section
open import Foundations.Total.Base

-- binary product
module _ {ma ℓ-oba⁻} {Oba⁻ : ob-sig ℓ-oba⁻} {na ℓ-oba⁺} {Oba⁺ : ob-sig ℓ-oba⁺}
  {ℓ-heta} (A : Quiver-onω ma Oba⁻ na Oba⁺ ℓ-heta)
  {mb ℓ-obb⁻} {Obb⁻ : ob-sig ℓ-obb⁻} {nb ℓ-obb⁺} {Obb⁺ : ob-sig ℓ-obb⁺}
  {ℓ-hetb} (B : Quiver-onω mb Obb⁻ nb Obb⁺ ℓ-hetb) where

  infixr 80 _×̫_
  _×̫_ : Quiver-onω (ma + mb) (λ ls → Oba⁻ _ ×ₜ Obb⁻ _) (na + nb) (λ ls → Oba⁺ _ ×ₜ Obb⁺ _) _
  _×̫_ = Σ̫[ Const A B ]


-- indexed product
module _ {ℓa} (A : Type ℓa)
  {m ℓ-ob⁻} {Ob⁻ : A → ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : A → ob-sig ℓ-ob⁺}
  {ℓ-het} (B : (x : A) → Quiver-onω m (Ob⁻ x) n (Ob⁺ x) ℓ-het) where
  private module B x = Quiver-onω (B x)

  infixr 60 Π̫ₜ ∀̫ₜ
  Π̫ₜ : Quiver-onω m (ΠOb (λ _ → A) Ob⁻) n (ΠOb (λ _ → A) Ob⁺) _
  Π̫ₜ .Quiver-onω.Het P Q = (x : A) → B.Het x (P x) (Q x)
  syntax Π̫ₜ X (λ x → F) = Π̫ₜ[ x ꞉ X ] F

  ∀̫ₜ : Quiver-onω m (∀Ob (λ _ → A) Ob⁻) n (∀Ob (λ _ → A) Ob⁺) _
  ∀̫ₜ .Quiver-onω.Het P Q = {x : A} → B.Het x (P {x}) (Q {x})
  syntax ∀̫ₜ X (λ x → F) = ∀̫ₜ[ x ꞉ X ] F


-- cotensor
module _ {ℓa} (A : Type ℓa)
  {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het} {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  (B : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω B) where

  infixr 10 _⋔̫ₜ_
  _⋔̫ₜ_ : Quiver-onω m (λ ls → A → Ob⁻ ls) n (λ ls → A → Ob⁺ ls) _
  _⋔̫ₜ_ = Π̫ₜ A (λ _ → B)

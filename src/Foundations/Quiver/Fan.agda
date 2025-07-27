{-# OPTIONS --safe #-}
module Foundations.Quiver.Fan where

open import Foundations.Quiver.Base

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} (C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω C) where

  Fan⁻ : ∀{lbs} (b : Ob⁺ lbs) las → Type (ℓ-ob⁻ las ⊔ ℓ-het las lbs)
  Fan⁻ b las = Σₜ (Ob⁻ las) λ a → Het a b

  Fan⁺ : ∀{las} (a : Ob⁻ las) lbs → Type (ℓ-ob⁺ lbs ⊔ ℓ-het las lbs)
  Fan⁺ a lbs = Σₜ (Ob⁺ lbs) λ b → Het a b

  Contractible⁻ : ∀ lcs ls → Type (ℓ-ob⁻ lcs ⊔ ℓ-ob⁺ ls ⊔ ℓ-het lcs ls)
  Contractible⁻ lcs ls = Σₜ (Ob⁻ lcs) λ centre → (x : Ob⁺ ls) → Het centre x

  Contractible⁺ : ∀ lcs ls → Type (ℓ-ob⁻ ls ⊔ ℓ-ob⁺ lcs ⊔ ℓ-het ls lcs)
  Contractible⁺ lcs ls = Σₜ (Ob⁺ lcs) λ centre → (x : Ob⁻ ls) → Het x centre

  Connected : ∀ lxs lys → Type (ℓ-ob⁻ lxs ⊔ ℓ-ob⁺ lys ⊔ ℓ-het lxs lys)
  Connected lxs lys = (x : Ob⁻ lxs) (y : Ob⁺ lys) → Het x y

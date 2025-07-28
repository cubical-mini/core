{-# OPTIONS --safe #-}
module Foundations.Quiver.Component where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {m′ ℓ-obᵈ⁻} {Ob[_]⁻ : ob-sigᵈ Ob ℓ-obᵈ⁻} {n′ ℓ-obᵈ⁺} {Ob[_]⁺ : ob-sigᵈ Ob ℓ-obᵈ⁺}
  {ℓ-hetᵈ} (D : SQuiver-onωᵈ C m′ Ob[_]⁻ n′ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D)
  ⦃ _ : Refl C ⦄ where

  module _ {ls} (t : Ob ls) where
    Component : Quiver-onω m′ Ob[ t ]⁻ n′ Ob[ t ]⁺ _
    Component .Quiver-onω.Het = Het[ refl ]


module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {m′ ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  {D : HQuiver-onωᵈ C m′ Ob[_] ℓ-homᵈ}
  ⦃ rd : Reflᵈ D ⦄ where instance

  Component-Refl : ∀{ls} {t : Ob ls} → Refl (Component D ⦃ rd .Reflᵈ.rfl ⦄ t) -- canonical way
  Component-Refl .refl = reflᵈ
  {-# INCOHERENT Component-Refl #-}

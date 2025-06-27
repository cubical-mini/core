{-# OPTIONS --safe #-}
module Foundations.Quiver.Component.Base where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {m′ n′ ℓ-obᵈ⁻ ℓ-obᵈ⁺ ℓ-hetᵈ} {Ob[_]⁻ : ob-sigᵈ Ob ℓ-obᵈ⁻} {Ob[_]⁺ : ob-sigᵈ Ob ℓ-obᵈ⁺}
  (D : Quiver-onωᵈ Ob Ob Hom m′ n′ Ob[_]⁻ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D)
  ⦃ _ : Reflω C ⦄ where

  module _ {ls} (t : Ob ls) where
    Component : Quiver-onω m′ n′ Ob[ t ]⁻ Ob[ t ]⁺ _
    Component .Quiver-onω.Het = Het[ refl ]

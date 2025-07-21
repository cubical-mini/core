{-# OPTIONS --safe #-}
module CC where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete
open import Foundations.Quiver.Exponential

module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} where
  𝒜 = Disc A
  ℬ = Disc B
  𝒜⇒ℬ = 𝒜 ⇒ ℬ

  module _ {f g : A → B} where
    open Quiver-onω 𝒜⇒ℬ renaming (Het to Hom)

    fun-ext-to : f ＝ g → Hom f g
    fun-ext-to α _ _ p i = α i (p i)

    fun-ext-from : Hom f g → f ＝ g
    fun-ext-from r i x = r _ _ (λ _ → x) i

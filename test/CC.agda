{-# OPTIONS --safe #-}
module CC where

open import Foundations.Base
open import Foundations.Discrete
open import Foundations.Exponential

module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} {f g : A → B} where
  𝒜→ℬ = Disc A →̫ Disc B
  open Quiver-onω 𝒜→ℬ renaming (Het to Hom)

  fun-ext-to : f ＝ g → Hom f g
  fun-ext-to α _ _ p i = α i (p i)

  fun-ext-from : Hom f g → f ＝ g
  fun-ext-from r i x = r _ _ (λ _ → x) i

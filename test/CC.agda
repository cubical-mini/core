{-# OPTIONS --safe #-}
module CC where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete
open import Foundations.Quiver.Exponential
open import Foundations.Quiver.Section

funs-on : HQuiver-onω 1 (λ (ℓ , tt) → Type ℓ) _
funs-on .Quiver-onω.Het A B = A → B

module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} where

  𝒜 : HQuiver-onω 0 (λ _ → A) (λ _ _ → ℓa)
  𝒜 = Disc A

  ℬ : HQuiver-onω 0 (λ _ → B) (λ _ _ → ℓb)
  ℬ = Disc B

  𝒜⇒ℬ : HQuiver-onω 0 (λ _ → A → B) (λ _ _ → ℓa ⊔ ℓb)
  𝒜⇒ℬ = 𝒜 ⇒ ℬ

  module _ {f g : A → B} where
    open Quiver-onω 𝒜⇒ℬ renaming (Het to Hom)

    fun-ext-to : f ＝ g → Hom f g
    fun-ext-to α _ _ p i = α i (p i)

    fun-ext-from : Hom f g → f ＝ g
    fun-ext-from r i x = r _ _ (λ _ → x) i

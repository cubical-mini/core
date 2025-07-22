{-# OPTIONS --safe #-}
module Foundations.Quiver.Const.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Const.Base

open import Notation.Comp
open import Notation.Refl
open import Notation.Sym

module _ {ma ℓ-oba ℓ-homa} {Oba : ob-sig ℓ-oba}
  {A : HQuiver-onω ma Oba ℓ-homa}
  {mb ℓ-obb ℓ-homb} {Obb : ob-sig ℓ-obb}
  {B : HQuiver-onω mb Obb ℓ-homb} where instance

  Const-Reflᵈ : ⦃ _ : Reflω A ⦄ ⦃ _ : Reflω B ⦄ → Reflωᵈ (Const A B)
  Const-Reflᵈ .reflᵈ _ = refl

  Const-Symᵈ : ⦃ _ : Symω A ⦄ ⦃ _ : Symω B ⦄ → Symωᵈ (Const A B)
  Const-Symᵈ .symᵈ = sym

  Const-HCompᵈ : ⦃ _ : HCompω A ⦄ ⦃ _ : HCompω B ⦄ → HCompωᵈ (Const A B)
  Const-HCompᵈ ._∙ᵈ_ = _∙_

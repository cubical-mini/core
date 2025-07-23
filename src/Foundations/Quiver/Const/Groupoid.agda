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

  Const-Reflᵈ : ⦃ _ : Refl A ⦄ ⦃ _ : Refl B ⦄ → Reflᵈ (Const A B)
  Const-Reflᵈ .reflᵈ = refl

  Const-Symᵈ : ⦃ _ : Sym A ⦄ ⦃ _ : Sym B ⦄ → Symᵈ (Const A B)
  Const-Symᵈ .symᵈ = sym

  Const-HCompᵈ : ⦃ _ : HComp A ⦄ ⦃ _ : HComp B ⦄ → HCompᵈ (Const A B)
  Const-HCompᵈ ._∙ᵈ_ = _∙_

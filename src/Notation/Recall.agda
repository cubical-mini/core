{-# OPTIONS --safe #-}
module Notation.Recall where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {ℓa} {A : Type ℓa} {m ℓ-ob ℓ-hom} {Ob : A → ob-sig ℓ-ob}
  (B : (a : A) → HQuiver-onω m (Ob a) ℓ-hom)
  ⦃ _ : ∀{a} → Refl (B a) ⦄ where
  private module B a = Quiver-onω (B a) renaming (Het to Hom)

  record Recall {ℓf ℓy} (f : (x : A) → Ob x ℓf) (x : A) (y : Ob x ℓy) : Type (ℓ-hom ℓf ℓy) where
    constructor mk-recall
    field recall-hom : B.Hom x (f x) y

  recall : ∀{ℓf} (f : (x : A) → Ob x ℓf) (x : A)
         → Recall f x (f x)
  recall f x = mk-recall refl

{-# OPTIONS --safe #-}
module Foundations.Diagram.Negation where

open import Foundations.Base
open import Foundations.Diagram.Exponential
open import Foundations.Diagram.Initial
open import Foundations.Diagram.Product.Binary
open import Foundations.Discrete.Base
open import Foundations.Lens.Pull.Base

open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  ⦃ _ : Refl C ⦄ ⦃ hp : ∀{lys} {y : Ob lys} → Pull C 0 (λ x → Disc (Hom x y)) ⦄
  {ℓ-×} ⦃ _ : Binary-products C C ℓ-× ⦄
  {ℓ-⇒} ⦃ _ : Cartesian-closed C ℓ-⇒ ⦄
  {ℓ-ini} {ls} ⦃ _ : Initial C ℓ-ini ls ⦄ where

  infixr 0 ¬_
  ¬_ : Ob ls → Ob (ℓ-⇒ ls ℓ-ini)
  ¬ X = X ⇒ ⊥

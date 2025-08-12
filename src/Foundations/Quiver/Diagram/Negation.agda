{-# OPTIONS --safe #-}
module Foundations.Quiver.Diagram.Negation where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Diagram.Exponential
open import Foundations.Quiver.Diagram.Initial
open import Foundations.Quiver.Diagram.Product.Binary
open import Foundations.Quiver.Discrete.Base
open import Foundations.Quiver.Lens.Pull.Base

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

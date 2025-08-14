{-# OPTIONS --safe #-}
module Foundations.Lens.Push.Assoc where

open import Foundations.Base
open import Foundations.Discrete.Base
open import Foundations.Lens.Push.Base

open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} {C : HQuiver-onω m Ob ℓ-hom}
  (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ} {F : ob-sigᵈ Ob ℓ-obᶠ} {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {α : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)}
  ⦃ _ : Refl C ⦄ (hp : HPush C k α)
  (hpr : ∀{lxs} {x : Ob lxs} → HPush C 0 λ t → Disc (Hom x t)) where
  private
    module α {ls} t = Quiver-onω (α {ls} t) renaming (Het to Hom)
    instance
      _ = hp
      _ : ∀{lxs} {x : Ob lxs} → HPush C 0 λ t → Disc (Hom x t)
      _ = hpr

  record RAssoc : Typeω where
    no-eta-equality
    field
      assoc-r : ∀{lxs lys lzs lfs} {x : Ob lxs} {y : Ob lys} {z : Ob lzs}
                (u : F x lfs) (p : Hom x y) (q : Hom y z)
              → α.Hom z (u ▷ (p ▷ q)) (u ▷ p ▷ q)

open RAssoc ⦃ ... ⦄ public
  using (assoc-r)
{-# DISPLAY RAssoc.assoc-r _ u p q = assoc-r u p q #-}

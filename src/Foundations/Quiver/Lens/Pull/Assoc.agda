{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Pull.Assoc where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete.Base
open import Foundations.Quiver.Lens.Pull.Base

open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} {C : HQuiver-onω m Ob ℓ-hom}
  (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ} {F : ob-sigᵈ Ob ℓ-obᶠ} {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {α : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)}
  ⦃ _ : Refl C ⦄ (hp : HPull C k α)
  (hpl : ∀{lys} {y : Ob lys} → HPull C 0 λ t → Disc (Hom t y))
  where
  private
    module α {ls} t = Quiver-onω (α {ls} t) renaming (Het to Hom)
    instance
      _ = hp
      _ : ∀{lys} {y : Ob lys} → HPull C 0 λ t → Disc (Hom t y)
      _ = hpl

  record LAssoc : Typeω where
    no-eta-equality
    field
      assoc-l : ∀{lxs lys lzs lfs} {x : Ob lxs} {y : Ob lys} {z : Ob lzs}
                (v : F z lfs) (p : Hom x y) (q : Hom y z)
              → α.Hom x (p ◁ q ◁ v) ((p ◁ q) ◁ v)

open LAssoc ⦃ ... ⦄ public
  using (assoc-l)
{-# DISPLAY LAssoc.assoc-l _ v p q = assoc-l v p q #-}

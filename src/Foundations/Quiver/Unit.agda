{-# OPTIONS --safe #-}
module Foundations.Quiver.Unit where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete.Base
open import Foundations.Quiver.Lens.Pull.Assoc
open import Foundations.Quiver.Lens.Pull.Base
open import Foundations.Quiver.Lens.Push.Assoc
open import Foundations.Quiver.Lens.Push.Base

open import Notation.Refl

⟙ : HQuiver-onω 0 (λ _ → ⊤ₜ) λ _ _ → lzero
⟙ .Quiver-onω.Het _ _ = ⊤ₜ

instance
  ⟙-Refl : Refl ⟙
  ⟙-Refl .refl = tt

-- TODO remove unit params?
-- do we even need these?
module _ {k ℓ-obᶠ ℓ-homᶠ}
  {F : ⊤ₜ → ob-sig ℓ-obᶠ}
  (α : (t : ⊤ₜ) → HQuiver-onω k (F t) ℓ-homᶠ)
  ⦃ _ : ∀{t} → Refl (α t) ⦄ where
  private module α t = Quiver-onω (α t) renaming (Het to Hom)

  module Trivial-Push where instance
    ⟙-Push : HPush ⟙ k α
    ⟙-Push .Push.rfl = ⟙-Refl
    ⟙-Push ._▷_ f _ = f
    ⟙-Push .push-refl = refl

    ⟙-RAssoc : RAssoc ⟙ α
    ⟙-RAssoc .RAssoc.hp = ⟙-Push
    ⟙-RAssoc .RAssoc.hpr .Push.rfl = ⟙-Refl
    ⟙-RAssoc .RAssoc.hpr ._▷_ = _
    ⟙-RAssoc .RAssoc.hpr .push-refl = refl
    ⟙-RAssoc .assoc-r _ _ _ = refl

  module Trivial-Pull where instance
    ⟙-Pull : HPull ⟙ k α
    ⟙-Pull .Pull.rfl = ⟙-Refl
    ⟙-Pull ._◁_ _ f = f
    ⟙-Pull .pull-refl = refl

    ⟙-LAssoc : LAssoc ⟙ α
    ⟙-LAssoc .LAssoc.hp = ⟙-Pull
    ⟙-LAssoc .LAssoc.hpl .Pull.rfl = ⟙-Refl
    ⟙-LAssoc .LAssoc.hpl ._◁_ = _
    ⟙-LAssoc .LAssoc.hpl .pull-refl = refl
    ⟙-LAssoc .assoc-l _ _ _ = refl

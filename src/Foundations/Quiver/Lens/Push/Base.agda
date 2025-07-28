{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Push.Base where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  k {ℓ-obᶠ ℓ-obᵍ} {F : ob-sigᵈ Ob ℓ-obᶠ} {G : ob-sigᵈ Ob ℓ-obᵍ}
  {ℓ-het : ℓ-sig 3 (m , k , k , _)}
  (α : ∀{ls} (t : Ob ls) → Quiver-onω k (F t) k (G t) (ℓ-het ls)) where
  private module α {ls} t = Quiver-onω (α {ls} t)

  record Push : Typeω where
    no-eta-equality
    infixl 300 _▷_
    field
      ⦃ rfl ⦄ : Refl C
      _▷_ : ∀{lxs lys lfs}{x : Ob lxs} {y : Ob lys} → F x lfs → Hom x y → G y lfs
      push-refl : ∀{ls lfs}{x : Ob ls} {u : F x lfs} → α.Het x u (u ▷ refl)

open Push ⦃ ... ⦄ public
  using (_▷_ ; push-refl)
{-# DISPLAY Push._▷_ _ u p = u ▷ p #-}
{-# DISPLAY Push.push-refl _ = push-refl #-}

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} (C : HQuiver-onω m Ob ℓ-hom)
  k {ℓ-obᶠ} {F : ob-sigᵈ Ob ℓ-obᶠ} {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  (α : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)) where
  HPush  = Push C k α


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k ℓ-obᶠ} {F : ob-sigᵈ Ob ℓ-obᶠ} {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {α : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)}
  ⦃ _ : HPush C k α ⦄ where

  infixr 400 _<$>_
  _<$>_ : ∀{lxs lys lfs} {x : Ob lxs} {y : Ob lys} → Hom x y → F x lfs → F y lfs
  _<$>_ f mx = mx ▷ f

  infixl 400 _<&>_
  _<&>_ : ∀{lxs lys lfs} {x : Ob lxs} {y : Ob lys} → F x lfs → Hom x y → F y lfs
  _<&>_ = _▷_

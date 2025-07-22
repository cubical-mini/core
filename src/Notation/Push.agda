{-# OPTIONS --safe #-}
module Notation.Push where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} (C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω C)
  k {ℓ-obᶠ : ℓ-sig 2 (m , k , _)} {ℓ-obᵍ : ℓ-sig 2 (n , k , _)}
  (F : ob-sigᵈ Ob⁻ ℓ-obᶠ) (G : ob-sigᵈ Ob⁺ ℓ-obᵍ) where

  record Push lxs lys lfs : Type
    (ℓ-ob⁻ lxs ⊔ ℓ-ob⁺ lys ⊔ ℓ-het lxs lys ⊔ ℓ-obᶠ lxs lfs ⊔ ℓ-obᵍ lys lfs) where
    no-eta-equality
    field push : {x : Ob⁻ lxs} {y : Ob⁺ lys} (p : Het x y) → F x lfs → G y lfs

    infixl 300 _▷_
    _▷_ : {x : Ob⁻ lxs} {y : Ob⁺ lys} → F x lfs → Het x y → G y lfs
    α ▷ p = push p α

  Pushω : Typeω
  Pushω = ∀{lxs lys lfs} → Push lxs lys lfs

open Push ⦃ ... ⦄ public
{-# DISPLAY Push.push _ p u = push p u #-}

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} (C : HQuiver-onω m Ob ℓ-hom) k where
  module _ {ℓ-obᶠ} (F : ob-sigᵈ Ob ℓ-obᶠ) where
    module _ {ℓ-obᵍ} (G : ob-sigᵈ Ob ℓ-obᵍ) where
      SPush  = Push C k F G
      SPushω = ∀{lxs lys lfs} → SPush lxs lys lfs

    HPush  = SPush F
    HPushω = ∀{lxs lys lfs} → HPush lxs lys lfs


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} (C : HQuiver-onω m Ob ℓ-hom)
  {k ℓ-obᶠ ℓ-obᵍ} {ℓ-het : ℓ-sig 3 (m , k , k , _)}
  {F : ob-sigᵈ Ob ℓ-obᶠ} {G : ob-sigᵈ Ob ℓ-obᵍ}
  (α : ∀{ls} (t : Ob ls) → Quiver-onω k (F t) k (G t) (ℓ-het ls))
  ⦃ _ : Reflω C ⦄ ⦃ _ : SPushω C k F G ⦄ where
  private module α {ls} t = Quiver-onω (α {ls} t)

  record Lawful-Push ls lfs : Type (ℓ-ob ls ⊔ ℓ-obᶠ ls lfs ⊔ ℓ-het ls lfs lfs) where
    no-eta-equality
    field push-refl : {x : Ob ls} {u : F x lfs} → α.Het x u (push refl u)

  Lawful-Pushω : Typeω
  Lawful-Pushω = ∀{ls lfs} → Lawful-Push ls lfs

open Lawful-Push ⦃ ... ⦄ public
{-# DISPLAY Lawful-Push.push-refl _ = push-refl #-}


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k ℓ-obᶠ} {F : ob-sigᵈ Ob ℓ-obᶠ}
  {lxs lys lfs} ⦃ _ : HPush C k F lxs lys lfs ⦄ where

  infixr 400 _<$>_
  _<$>_ : {x : Ob lxs} {y : Ob lys} → Hom x y → F x lfs → F y lfs
  _<$>_ f mx = push f mx

  infixl 400 _<&>_
  _<&>_ : {x : Ob lxs} {y : Ob lys} → F x lfs → Hom x y → F y lfs
  _<&>_ mx f = push f mx

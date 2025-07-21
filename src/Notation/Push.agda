{-# OPTIONS --safe #-}
module Notation.Push where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} (C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω C)
  k {ℓ-obᶠ⁻ : ℓ-sig 2 (m , k , _)} {ℓ-obᶠ⁺ : ℓ-sig 2 (n , k , _)}
  (Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᶠ⁻) (Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᶠ⁺) where

  record Push lxs lys lfs : Type
    (ℓ-ob⁻ lxs ⊔ ℓ-ob⁺ lys ⊔ ℓ-het lxs lys ⊔ ℓ-obᶠ⁻ lxs lfs ⊔ ℓ-obᶠ⁺ lys lfs) where
    no-eta-equality
    field push : {x : Ob⁻ lxs} {y : Ob⁺ lys} (p : Het x y) → Ob[ x ]⁻ lfs → Ob[ y ]⁺ lfs

    infixl 300 _▷_
    _▷_ : {x : Ob⁻ lxs} {y : Ob⁺ lys} → Ob[ x ]⁻ lfs → Het x y → Ob[ y ]⁺ lfs
    α ▷ p = push p α

  Pushω : Typeω
  Pushω = ∀{lxs lys lfs} → Push lxs lys lfs

open Push ⦃ ... ⦄ public
{-# DISPLAY Push.push _ p u = push p u #-}

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} (C : HQuiver-onω m Ob ℓ-hom) k where
  module _ {ℓ-obᶠ⁻ ℓ-obᶠ⁺} (Ob[_]⁻ : ob-sigᵈ Ob ℓ-obᶠ⁻) (Ob[_]⁺ : ob-sigᵈ Ob ℓ-obᶠ⁺) where
    SPush = Push C k Ob[_]⁻ Ob[_]⁺
    SPushω = ∀{lxs lys lfs} → SPush lxs lys lfs

  module _ {ℓ-obᶠ} (Ob[_] : ob-sigᵈ Ob ℓ-obᶠ) where
    HPush = SPush Ob[_] Ob[_]
    HPushω = ∀{lxs lys lfs} → HPush lxs lys lfs


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} (C : HQuiver-onω m Ob ℓ-hom)
  {k ℓ-obᶠ⁻ ℓ-obᶠ⁺} {ℓ-hetᶠ : ℓ-sig 3 (m , k , k , _)}
  {Ob[_]⁻ : ob-sigᵈ Ob ℓ-obᶠ⁻} {Ob[_]⁺ : ob-sigᵈ Ob ℓ-obᶠ⁺}
  (F : ∀{ls} (t : Ob ls) → Quiver-onω k Ob[ t ]⁻ k Ob[ t ]⁺ (ℓ-hetᶠ ls))
  ⦃ _ : Reflω C ⦄ ⦃ _ : SPushω C k Ob[_]⁻ Ob[_]⁺ ⦄ where
  private module F {ls} t = Quiver-onω (F {ls} t)

  record Lawful-Push ls lfs : Type (ℓ-ob ls ⊔ ℓ-obᶠ⁻ ls lfs ⊔ ℓ-hetᶠ ls lfs lfs) where
    no-eta-equality
    field push-refl : {x : Ob ls} {u : Ob[ x ]⁻ lfs} → F.Het x u (push refl u)

  Lawful-Pushω : Typeω
  Lawful-Pushω = ∀{ls lfs} → Lawful-Push ls lfs

open Lawful-Push ⦃ ... ⦄ public
{-# DISPLAY Lawful-Push.push-refl _ = push-refl #-}


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k ℓ-obᶠ} {Ob[_] : ob-sigᵈ Ob ℓ-obᶠ}
  {lxs lys lfs} ⦃ _ : HPush C k Ob[_] lxs lys lfs ⦄ where

  infixr 400 _<$>_
  _<$>_ : {x : Ob lxs} {y : Ob lys} → Hom x y → Ob[ x ] lfs → Ob[ y ] lfs
  _<$>_ f mx = push f mx

  infixl 400 _<&>_
  _<&>_ : {x : Ob lxs} {y : Ob lys} → Ob[ x ] lfs → Hom x y → Ob[ y ] lfs
  _<&>_ mx f = push f mx

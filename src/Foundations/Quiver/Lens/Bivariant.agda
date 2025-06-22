{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Bivariant where

open import Foundations.Quiver.Base

open import Notation.Lens.Bivariant
open import Notation.Lens.Contravariant
open import Notation.Lens.Covariant
open import Notation.Refl

module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m : ℕ} {ℓ-obᶠ : Levels n → Levels n → ℓ-sig m} {ℓ-homᶠ : Levels n → Levels n → ℓ-sig² m}
  (F : {lxs lys : Levels n} {x : Ob lxs} {y : Ob lys} → Hom x y → Quiverω m (ℓ-obᶠ lxs lys) (ℓ-homᶠ lxs lys))
  ⦃ _ : Reflω C ⦄
  where
  private module F {lxs} {lys} x y p = Quiverω (F {lxs} {lys} {x} {y} p)

  Disp± : ⦃ _ : Extendω C F ⦄ → Quiverωᵈ C m _ _
  Disp± .Quiverωᵈ.Ob[_] t = F.Ob t t refl
  Disp± .Quiverωᵈ.Hom[_] {x} {y} p u v = F.Hom x y p (extend-l p u) (extend-r p v)


module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m : ℕ} {ℓ-obᶠ : Levels n → ℓ-sig m} {ℓ-homᶠ : Levels n → ℓ-sig² m}
  {F : {ls : Levels n} → Ob ls → Quiverω m (ℓ-obᶠ ls) (ℓ-homᶠ ls)}
  ⦃ _ : Reflω C ⦄
  where
  private module F {ls} x = Quiverω (F {ls} x)

  module _ ⦃ _ : Pushω C F ⦄ where instance
    Push→Extend : Extendω C (λ {y = y} _ → F y)
    Push→Extend .extend-l = push
    Push→Extend .extend-r _ v = v

    Lawful-Push→Extend : ⦃ _ : Lawful-Pushω C F ⦄ ⦃ _ : ∀{ls} {x : Ob ls} → Reflω (F x) ⦄
                       → Lawful-Extendω C (λ {y = y} _ → F y)
    Lawful-Push→Extend .extend-refl = push-refl
    Lawful-Push→Extend .extend-coh = refl

  module _ ⦃ _ : Pullω C F ⦄ where instance
    Pull→Extend : Extendω C (λ {x = x} _ → F x)
    Pull→Extend .extend-l _ u = u
    Pull→Extend .extend-r = pull

    Lawful-Pull→Extend : ⦃ _ : Lawful-Pullω C F ⦄ → Lawful-Extendω C (λ {x = x} _ → F x)
    Lawful-Pull→Extend .extend-refl = pull-refl
    Lawful-Pull→Extend .extend-coh = pull-refl

{-# OVERLAPPABLE
  Push→Extend Lawful-Push→Extend
  Pull→Extend Lawful-Pull→Extend
#-}


module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m : ℕ} {ℓ-obᶠ : Levels n → Levels n → ℓ-sig m} {ℓ-homᶠ : Levels n → Levels n → ℓ-sig² m}
  (F : {lxs lys : Levels n} {x : Ob lxs} {y : Ob lys} → Hom x y → Quiverω m (ℓ-obᶠ lxs lys) (ℓ-homᶠ lxs lys))
  ⦃ r : Reflω C ⦄ ⦃ e : Extendω C F ⦄ ⦃ _ : Lawful-Extendω C F ⦄
  where instance

  Disp±-Reflᵈ : Reflωᵈ C (Disp± F)
  Disp±-Reflᵈ .reflᵈ _ = extend-refl ⦃ r ⦄ ⦃ e ⦄
  {-# OVERLAPS Disp±-Reflᵈ #-} -- TODO check

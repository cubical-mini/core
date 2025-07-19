{-# OPTIONS --safe #-}
module Foundations.Quiver.Dual.Lens where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Dual.Base
open import Foundations.Quiver.Dual.Groupoid

open import Notation.Profunctor
open import Notation.Pull
open import Notation.Push
open import Notation.Refl

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom}
  {n} {ℓ-obᶠ⁻ ℓ-obᶠ⁺ : Levels m → ℓ-sig n}
  {Ob[_]⁻ : ob-sigᵈ Ob ℓ-obᶠ⁻} {Ob[_]⁺ : ob-sigᵈ Ob ℓ-obᶠ⁺}
  where instance

  Dual-Push : ⦃ _ : Pullω C n Ob[_]⁻ Ob[_]⁺ ⦄ → Pushω (Op C) n Ob[_]⁺ Ob[_]⁻
  Dual-Push .push = pull

  Dual-Pull : ⦃ _ : Pushω C n Ob[_]⁻ Ob[_]⁺ ⦄ → Pullω (Op C) n Ob[_]⁺ Ob[_]⁻
  Dual-Pull .pull = push

  module _ {ℓ-hetᶠ : Levels m → ℓ-sig² n n}
    {F : ∀{ls} (t : Ob ls) → Quiver-onω n n Ob[ t ]⁻ Ob[ t ]⁺ (ℓ-hetᶠ ls)}
    ⦃ _ : Reflω C ⦄ where instance

    Dual-Push-Lawful : ⦃ _ : Pullω C n Ob[_]⁻ Ob[_]⁺ ⦄ ⦃ lp : Lawful-Pullω C F ⦄
                     → Lawful-Pushω (Op C) (λ t → Op (F t))
    Dual-Push-Lawful ⦃ lp ⦄ .push-refl = lp .Lawful-Pull.pull-refl

    Dual-Pull-Lawful : ⦃ _ : Pushω C n Ob[_]⁻ Ob[_]⁺ ⦄ ⦃ lp : Lawful-Pushω C F ⦄
                     → Lawful-Pullω (Op C) (λ t → Op (F t))
    Dual-Pull-Lawful ⦃ lp ⦄ .pull-refl = lp .Lawful-Push.push-refl


module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-hom⁻ ℓ-hom⁺} {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  {A : HQuiver-onω m Ob⁻ ℓ-hom⁻} {B : HQuiver-onω n Ob⁺ ℓ-hom⁺}
  {k} {ℓ-hetᶠ ℓ-hetᵍ : Levels m → Levels n → ℓ-sig k}
  {F : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᶠ} {G : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᵍ} where instance

  Dual-Profunctor : ⦃ pr : Profunctorω A B k F G ⦄
                  → Profunctorω (Op B) (Op A) k (λ y x → F x y) (λ y x → G x y)
  Dual-Profunctor .dimap p q = dimap q p

  module _
    {ℓ-hetʰ : Levels m → Levels n → ℓ-sig² k k}
    {H : ∀{lxs lys} (x : Ob⁻ lxs) (y : Ob⁺ lys) → Quiver-onω k k (F x y) (G x y) (ℓ-hetʰ lxs lys)}
    ⦃ _ : Reflω A ⦄ ⦃ _ : Reflω B ⦄ ⦃ _ : Profunctorω A B k F G ⦄ where instance

    Dual-Profunctor-Lawful : ⦃ lp : Lawful-Profunctorω A B H ⦄ → Lawful-Profunctorω (Op B) (Op A) (λ y x → H x y)
    Dual-Profunctor-Lawful ⦃ lp ⦄ .dimap-refl = lp .Lawful-Profunctor.dimap-refl

-- TODO check pragmas
{-# INCOHERENT
  Dual-Push Dual-Pull
  Dual-Push-Lawful Dual-Pull-Lawful
  Dual-Profunctor
  Dual-Profunctor-Lawful
#-}

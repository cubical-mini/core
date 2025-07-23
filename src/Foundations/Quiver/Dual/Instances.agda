{-# OPTIONS --safe #-}
module Foundations.Quiver.Dual.Instances where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Dual.Base

open import Notation.Profunctor
open import Notation.Pull
open import Notation.Push
open import Notation.Refl
open import Notation.Sym

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} where instance

  Dual-Refl : ⦃ r : Refl C ⦄ → Refl (C ᵒᵖ)
  Dual-Refl ⦃ r ⦄ .refl = r .Refl.refl

  Dual-Sym : ∀{ℓf} {F : ∀{lxs lys} (x : Ob lxs) (y : Ob lys) → HQuiver-onω 0 _ ℓf}
             ⦃ s : Sym C F ⦄ → Sym (C ᵒᵖ) λ x y → F y x
  Dual-Sym ⦃ s ⦄ .sym = s .Sym.sym
  Dual-Sym ⦃ s ⦄ .sym-invol = s .Sym.sym-invol


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} {C : HQuiver-onω m Ob ℓ-hom}
  {m′ ℓ-obᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ} {ℓ-homᵈ}
  {D : HQuiver-onωᵈ C m′ Ob[_] ℓ-homᵈ} where instance

  Dual-Reflᵈ : ⦃ _ : Refl C ⦄ ⦃ r′ : Reflᵈ D ⦄ → Reflᵈ (D ᵒᵖᵈ)
  Dual-Reflᵈ ⦃ r′ ⦄ .reflᵈ = r′ .Reflᵈ.reflᵈ


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} {C : HQuiver-onω m Ob ℓ-hom}
  {k ℓ-obᶠ ℓ-obᵍ} {F : ob-sigᵈ Ob ℓ-obᶠ} {G : ob-sigᵈ Ob ℓ-obᵍ}
  {ℓ-hetᶠ : ℓ-sig 3 (m , k , k , _)}
  {α : ∀{ls} (t : Ob ls) → Quiver-onω k (F t) k (G t) (ℓ-hetᶠ ls)}
  ⦃ _ : Refl C ⦄ where instance

  Dual-Push : ⦃ _ : Pull C k α ⦄ → Push (C ᵒᵖ) k (λ t → α t ᵒᵖ)
  Dual-Push .push = pull
  Dual-Push .push-refl = pull-refl

  Dual-Pull : ⦃ pp : Push C k α ⦄ → Pull (C ᵒᵖ) k (λ t → α t ᵒᵖ)
  Dual-Pull .pull = push
  Dual-Pull ⦃ pp ⦄ .pull-refl = pp .Push.push-refl


module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-hom⁻ ℓ-hom⁺}
  {A : HQuiver-onω m Ob⁻ ℓ-hom⁻} {B : HQuiver-onω n Ob⁺ ℓ-hom⁺}
  {k} {ℓ-hetᶠ ℓ-hetᵍ : ℓ-sig 3 (m , n , k , _)}
  {F : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᶠ} {G : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᵍ}
  {ℓ-hetʰ : ℓ-sig 4 (m , n , k , k , _)}
  {α : ∀{lxs lys} (x : Ob⁻ lxs) (y : Ob⁺ lys) → Quiver-onω k (F x y) k (G x y) (ℓ-hetʰ lxs lys)}
  ⦃ _ : Refl A ⦄ ⦃ _ : Refl B ⦄ where instance

  Dual-Profunctor : ⦃ pp : Profunctor A B k α ⦄ → Profunctor (B ᵒᵖ) (A ᵒᵖ) k (λ y x → α x y)
  Dual-Profunctor .dimap p q = dimap q p
  Dual-Profunctor ⦃ pp ⦄ .dimap-refl = pp .Profunctor.dimap-refl

-- TODO check pragmas
{-# INCOHERENT
  Dual-Push Dual-Pull
  Dual-Profunctor
#-}

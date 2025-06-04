{-# OPTIONS --safe #-}
module Notation.Displayed.Push where

open import Prim.Type

open import Notation.Base
open import Notation.Displayed.Base
open import Notation.Displayed.Push.Base public
open import Notation.Displayed.Reflexivity
open import Notation.Reflexivity

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  {ℓ-obᵈ : ℓ-ob-sig} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ)
  {ℓ-homᵈ : ℓ-hom-sig} (F : ∀{ℓ} (t : Ob ℓ) → Quiver-on (λ _ → Ob[ t ]) (λ _ _ → ℓ-homᵈ ℓ ℓ))
  ⦃ _ : Reflω C ⦄ ⦃ _ : Pushω C Ob[_] ⦄ where
  private module F {ℓ} t = Quiver-on (F {ℓ} t)

  record Push-Id ℓ : Type (ℓ-ob ℓ l⊔ ℓ-obᵈ ℓ l⊔ ℓ-homᵈ ℓ ℓ) where
    no-eta-equality
    field push-id : {x : Ob ℓ} {x′ : Ob[ x ]} → F.Hom x {ℓx = ℓ} {ℓy = ℓ} (push refl x′) x′
    -- TODO check levels

  Push-Idω : Typeω
  Push-Idω = ∀{ℓ} → Push-Id ℓ

open Push-Id ⦃ ... ⦄ public

{-# DISPLAY Push-Id.push-id _ = push-id #-}


module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓ-obᵈ : ℓ-ob-sig} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  {ℓ-homᵈ : ℓ-hom-sig} {F : ∀{ℓ} (t : Ob ℓ) → Quiver-on (λ _ → Ob[ t ]) (λ _ _ → ℓ-homᵈ ℓ ℓ)}
  ⦃ _ : Reflω C ⦄ ⦃ _ : Pushω C Ob[_] ⦄ ⦃ _ : Push-Idω C Ob[_] {ℓ-homᵈ} F ⦄
  where instance

  Push-Refl : Reflᵈω C (Disp⁺ C Ob[_] {ℓ-homᵈ} F)
  Push-Refl .reflᵈ {x} {x′} = push-id
  -- {-# INCOHERENT #-} -- TODO check

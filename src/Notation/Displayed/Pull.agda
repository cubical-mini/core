{-# OPTIONS --safe #-}
module Notation.Displayed.Pull where

open import Prim.Type

open import Notation.Base
open import Notation.Displayed.Base
open import Notation.Displayed.Pull.Base public
open import Notation.Displayed.Reflexivity
open import Notation.Reflexivity

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  {ℓ-obᵈ : ℓ-ob-sig} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ)
  {ℓ-homᵈ : ℓ-hom-sig} (F : ∀{ℓ} (t : Ob ℓ) → Quiver-on (λ _ → Ob[ t ]) (λ _ _ → ℓ-homᵈ ℓ ℓ))
  ⦃ _ : Reflω C ⦄ ⦃ _ : Pullω C Ob[_] ⦄ where
  private module F {ℓ} t = Quiver-on (F {ℓ} t)

  record Pull-Id ℓ : Type (ℓ-ob ℓ l⊔ ℓ-obᵈ ℓ l⊔ ℓ-homᵈ ℓ ℓ) where
    no-eta-equality
    field pull-id : {x : Ob ℓ} {x′ : Ob[ x ]} → F.Hom x {ℓx = ℓ} {ℓy = ℓ} x′ (pull refl x′)
    -- TODO check levels

  Pull-Idω : Typeω
  Pull-Idω = ∀{ℓ} → Pull-Id ℓ

open Pull-Id ⦃ ... ⦄ public

{-# DISPLAY Pull-Id.pull-id _ = pull-id #-}


module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓ-obᵈ : ℓ-ob-sig} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  {ℓ-homᵈ : ℓ-hom-sig} {F : ∀{ℓ} (t : Ob ℓ) → Quiver-on (λ _ → Ob[ t ]) (λ _ _ → ℓ-homᵈ ℓ ℓ)}
  ⦃ _ : Reflω C ⦄ ⦃ _ : Pullω C Ob[_] ⦄ ⦃ _ : Pull-Idω C Ob[_] {ℓ-homᵈ} F ⦄
  where instance

  Pull-Refl : Reflᵈω C (Disp⁻ C Ob[_] {ℓ-homᵈ} F)
  Pull-Refl .reflᵈ {x} {x′} = pull-id
  -- {-# INCOHERENT #-} -- TODO check

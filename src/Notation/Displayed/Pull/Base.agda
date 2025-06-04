{-# OPTIONS --safe #-}
module Notation.Displayed.Pull.Base where

open import Prim.Type

open import Notation.Base
open import Notation.Displayed.Base

-- family of quivers
module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  {ℓ-obᵈ : ℓ-ob-sig} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ) where

  record Pull ℓx ℓy : Type (ℓ-ob ℓx l⊔ ℓ-ob ℓy l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-obᵈ ℓx l⊔ ℓ-obᵈ ℓy) where
    no-eta-equality
    field pull : {x : Ob ℓx} {y : Ob ℓy} (p : Hom x y) → Ob[ y ] → Ob[ x ]

  Pullω : Typeω
  Pullω = ∀{ℓx ℓy} → Pull ℓx ℓy

open Pull ⦃ ... ⦄ public

{-# DISPLAY Pull.pull _ p y′ = pull p y′ #-}


module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  {ℓ-obᵈ : ℓ-ob-sig} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ)
  {ℓ-homᵈ : ℓ-hom-sig} (F : ∀{ℓ} (t : Ob ℓ) → Quiver-on (λ _ → Ob[ t ]) (λ _ _ → ℓ-homᵈ ℓ ℓ))
  ⦃ _ : Pullω C Ob[_] ⦄ where
  private module F {ℓ} t = Quiver-on (F {ℓ} t)

  Disp⁻ : Quiver-onᵈ C Ob[_] _
  Disp⁻ .Quiver-onᵈ.Hom[_] {ℓx} {ℓy} {x} {y} f x′ y′ = F.Hom x {ℓx = ℓx} {ℓy = ℓx} x′ (pull f y′)
  -- TODO check levels

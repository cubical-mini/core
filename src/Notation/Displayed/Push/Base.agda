{-# OPTIONS --safe #-}
module Notation.Displayed.Push.Base where

open import Prim.Type

open import Notation.Base
open import Notation.Displayed.Base

-- family of quivers
module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  {ℓ-obᵈ : ℓ-ob-sig} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ) where

  record Push ℓx ℓy : Type (ℓ-ob ℓx l⊔ ℓ-ob ℓy l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-obᵈ ℓx l⊔ ℓ-obᵈ ℓy) where
    no-eta-equality
    field push : {x : Ob ℓx} {y : Ob ℓy} (p : Hom x y) → Ob[ x ] → Ob[ y ]

  Pushω : Typeω
  Pushω = ∀{ℓx ℓy} → Push ℓx ℓy

open Push ⦃ ... ⦄ public

{-# DISPLAY Push.push _ p x′ = push p x′ #-}


module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  {ℓ-obᵈ : ℓ-ob-sig} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ)
  {ℓ-homᵈ : ℓ-hom-sig} (F : ∀{ℓ} (t : Ob ℓ) → Quiver-on (λ _ → Ob[ t ]) (λ _ _ → ℓ-homᵈ ℓ ℓ))
  ⦃ _ : Pushω C Ob[_] ⦄ where
  private module F {ℓ} t = Quiver-on (F {ℓ} t)

  Disp⁺ : Quiver-onᵈ C Ob[_] _
  Disp⁺ .Quiver-onᵈ.Hom[_] {ℓx} {_} {x} {y} f x′ y′ = F.Hom y {ℓx = ℓx} {ℓy = ℓx} (push f x′) y′
  -- TODO check levels

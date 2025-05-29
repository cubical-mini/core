{-# OPTIONS --safe #-}
module Foundations.IdentitySystem where

open import Prim.Kan
open import Prim.Type

open import Foundations.HLevel.Base

open import Notation.Base
open import Notation.Initial.Wild
open import Notation.Reflexivity

open import Prim.Data.Sigma

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  (ℓ : Level) ⦃ _ : Refl C ℓ ⦄ where

  record is-identity-system : Typeω where
    no-eta-equality
    field
      to-path : {x y : Ob ℓ} → Hom x y → x ＝ y
      to-path-over
        : {x y : Ob ℓ} (p : Hom x y)
        → Pathᴾ (λ i → Hom x (to-path p i)) refl p

    eww : {x : Ob ℓ} → is-contr (Σₜ (Ob ℓ) (Hom x))
    eww {x} .Wild-initial.source = x , refl
    eww .Wild-initial.from-source {x′ , p} i = to-path p i , to-path-over p i

    -- Fan : (ℓ : Level) {ℓc : Level} {c : Ob ℓc} →  Type (ℓ-ob ℓ l⊔ ℓ-hom ℓc ℓ)
    -- Fan ℓ {ℓc} {c} = Σₜ (Ob ℓ) (λ w → Hom c w)

    -- Cofan : (ℓ : Level) {ℓc : Level} {c : Ob ℓc} →  Type (ℓ-ob ℓ l⊔ ℓ-hom ℓ ℓc)
    -- Cofan ℓ {ℓc} {c} = Σₜ (Ob ℓ) (λ w → Hom w c)

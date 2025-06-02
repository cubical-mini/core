{-# OPTIONS --safe #-}
module Foundations.IdentitySystem.Base where

open import Prim.Kan
open import Prim.Type

module _ {ℓ ℓr} {A : Type ℓ} (R : A → A → Type ℓr) (rfl : ∀ a → R a a) where
  record is-identity-system : Type (ℓ l⊔ ℓr) where
    no-eta-equality
    field
      to-path : {x y : A} → R x y → x ＝ y
      to-path-over
        : {x y : A} (p : R x y)
        → Pathᴾ (λ i → R x (to-path p i)) (rfl x) p

-- instance
--   path-ids : ∀{ℓa} {A : Type ℓa} → is-identity-system (Path A) λ _ → reflₚ
--   path-ids .is-identity-system.to-path p = p
--   path-ids .is-identity-system.to-path-over p i j = p (i ∧ j)

-- record fibre {ℓa ℓr ℓb} {A : Type ℓa} {B : Type ℓb}
--     {R : B → B → Type ℓr} {rfl : ∀ b → R b b}
--     ⦃ ids : is-identity-system R rfl ⦄
--     (f : A → B) (y : B) : Type (ℓa l⊔ ℓr) where
--   no-eta-equality
--   field
--     preimage : A
--     maps-to  : R (f preimage) y

-- fibreₚ : ∀{ℓa ℓb} {A : Type ℓa} {B : Type ℓb} (f : A → B) (y : B) → Type (ℓa l⊔ ℓb)
-- fibreₚ f y = fibre f y

-- --     eww : {x : Ob ℓ} → is-contr (Σ (Ob ℓ) (Hom x))
-- --     eww .centre = _ , refl
-- --     eww .centre-cell (x′ , p) i = to-path p i , to-path-over p i

-- --     -- Fan : (ℓ : Level) {ℓc : Level} {c : Ob ℓc} →  Type (ℓ-ob ℓ l⊔ ℓ-hom ℓc ℓ)
-- --     -- Fan ℓ {ℓc} {c} = Σₜ (Ob ℓ) (λ w → Hom c w)

-- --     -- Cofan : (ℓ : Level) {ℓc : Level} {c : Ob ℓc} →  Type (ℓ-ob ℓ l⊔ ℓ-hom ℓ ℓc)
-- --     -- Cofan ℓ {ℓc} {c} = Σₜ (Ob ℓ) (λ w → Hom w c)

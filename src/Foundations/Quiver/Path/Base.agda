{-# OPTIONS --safe #-}
module Foundations.Quiver.Path.Base where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Component
open import Foundations.Quiver.Discrete.Base
open import Foundations.Quiver.Fan

open import Notation.Refl

module _ {ℓo ℓh} {Ob : Type ℓo}
  (C : HQuiver-onω 0 (λ _ → Ob) (λ _ _ → ℓh)) (open Quiver-onω C renaming (Het to Hom))
  ⦃ _ : Refl C ⦄ where

  record is-path-object : Type (ℓo ⊔ ℓh) where
    no-eta-equality
    field
      to-path : {x y : Ob} → Hom x y → x ＝ y
      to-path-over : {x y : Ob} (p : Hom x y)
                   → Pathᴾ (λ i → Hom x (to-path p i)) refl p

    -- FIXME
    -- fan⁺-is-contr⁺ : {t : Ob} → is-contr⁺ (Fan⁺ C t _)
    -- fan⁺-is-contr⁺ {t} .fst = t , refl
    -- fan⁺-is-contr⁺     .snd (_ , q) i = to-path q i , to-path-over q i


open is-path-object public


module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom}
  {ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  (D : HQuiver-onωᵈ C 0 Ob[_] ℓ-homᵈ)
  ⦃ _ : Refl C ⦄ ⦃ _ : Reflᵈ D ⦄ where

  is-path-objectᵈ : ∀ ls → Type (ℓ-ob ls ⊔ ℓ-obᵈ ls _ ⊔ ℓ-homᵈ ls ls _ _)
  is-path-objectᵈ ls = {t : Ob ls} → is-path-object (Component D t)

  is-path-objectωᵈ : Typeω
  is-path-objectωᵈ = ∀{ls} → is-path-objectᵈ ls


module _ {ℓa ℓh} (A : Type ℓa)
  {C : HQuiver-onω 0 (λ _ → A) λ _ _ → ℓh} (open Quiver-onω C renaming (Het to Hom))
  ⦃ _ : Refl C ⦄ (po : is-path-object C) where

  is-contr⁻ is-contr⁺ is-prop : Type (ℓa ⊔ ℓh)

  is-contr⁻ = Contractible⁻ C _ _
  is-contr⁺ = Contractible⁺ C _ _
  is-prop   = Connected     C _ _
  {-# NOINLINE is-contr⁻ #-}
  {-# NOINLINE is-contr⁺ #-}
  {-# NOINLINE is-prop   #-}

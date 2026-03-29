module Foundations.Path.Base where

open import Foundations.Base
open import Foundations.Component
open import Foundations.Discrete.Base

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
    -- fan⁺-is-contr⁺ : {t : Ob} → is-contr~⁺ (Fan⁺ C t _)
    -- fan⁺-is-contr⁺ {t} .fst = t , refl
    -- fan⁺-is-contr⁺     .snd (_ , q) i = to-path q i , to-path-over q i


open is-path-object public


module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom}
  {ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  (D : HQuiver-onωᵈ C 0 Ob[_] ℓ-homᵈ)
  ⦃ _ : Refl C ⦄ ⦃ _ : Reflᵈ D ⦄ where

  is-path-objectᵈ : Typeω
  is-path-objectᵈ = ∀{ls} {t : Ob ls} → is-path-object (Component D t)


discrete-path-object : ∀{ℓ} (A : Type ℓ) → is-path-object (Disc A)
discrete-path-object _ .to-path p = p
discrete-path-object _ .to-path-over p i j = p (i ∧ j)

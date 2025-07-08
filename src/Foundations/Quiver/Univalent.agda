{-# OPTIONS --safe --erased-cubical #-}
module Foundations.Quiver.Univalent where

open import Prim.Kan

open import Foundations.Quiver.Base
open import Foundations.Quiver.Component.Base
open import Foundations.Quiver.Component.Groupoid

open import Notation.Refl

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  ⦃ _ : Reflω C ⦄ where

  record is-univalent ls : Type (ℓ-ob ls ⊔ ℓ-hom ls ls) where
    no-eta-equality
    field
      to-path : {x y : Ob ls} → Hom x y → x ＝ y
      to-path-over : {x y : Ob ls} (p : Hom x y)
                   → Pathᴾ (λ i → Hom x (to-path p i)) refl p

  is-univalentω : Typeω
  is-univalentω = ∀{ls} → is-univalent ls


module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom}
  {m′ ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  (D : HQuiver-onωᵈ Ob _ m′ Ob[_] ℓ-homᵈ)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Reflωᵈ C D ⦄ where

  is-univalentᵈ : ∀ ls lsᵈ → Type (ℓ-ob ls ⊔ ℓ-obᵈ ls lsᵈ ⊔ ℓ-homᵈ ls ls lsᵈ lsᵈ)
  is-univalentᵈ ls lsᵈ = {t : Ob ls} → is-univalent (Component D t) lsᵈ

  is-univalentωᵈ : Typeω
  is-univalentωᵈ = ∀{ls lsᵈ} → is-univalentᵈ ls lsᵈ

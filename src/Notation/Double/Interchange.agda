{-# OPTIONS --safe #-}
module Notation.Double.Interchange where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Double.Base
open import Notation.Double.Composition

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-sq : ℓ-sq-sig}
  (C : ℚuiver-on Ob ℓ-sq) (open ℚuiver-on C)
  ⦃ _ : Compω Quiverₕ ⦄ ⦃ _ : Compω Quiverᵥ ⦄ ⦃ _ : ∀{ℓw ℓx ℓy ℓz ℓu ℓv} → ℂomp C ℓw ℓx ℓy ℓz ℓu ℓv ⦄
  (_~_ : ∀{ℓw ℓx ℓy ℓz} {w : Ob ℓw} {x : Ob ℓx} {f : Hor w x} {y : Ob ℓy} {g : Ver w y} {z : Ob ℓz} {h : Ver x z} {k : Hor y z} (α β : Sq f g h k) → Type (ℓ-sq ℓw ℓx ℓy ℓz)) where
  -- ^ TODO 2-sq-sig

  record 𝕀nterchange : Typeω where
    no-eta-equality
    field
      interchange : {ℓa ℓb ℓc ℓd ℓe ℓf ℓg ℓh ℓk : Level}
                    {A : Ob ℓa} {B : Ob ℓb} {f : Hor A B} {C : Ob ℓc} {g : Ver A C} {D : Ob ℓd}
                    {h : Ver B D} {k : Hor C D} (α : Sq f g h k)
                    {E : Ob ℓe} {l : Hor B E} {F : Ob ℓf}
                    {m : Ver E F} {n : Hor D F} (β : Sq l h m n)
                    {G : Ob ℓg} {o : Ver C G} {H : Ob ℓh}
                    {p : Ver D H} {q : Hor G H} (γ : Sq k o p q)
                    {K : Ob ℓk} {r : Ver F K} {s : Hor H K} (δ : Sq n p r s)
                  → (α ∙ᵥ γ) ∙ₕ (β ∙ᵥ δ) ~ (α ∙ₕ β) ∙ᵥ (γ ∙ₕ δ)

open 𝕀nterchange ⦃ ... ⦄ public

{-# DISPLAY 𝕀nterchange.interchange _ α β γ δ = interchange α β γ δ #-}

{-# OPTIONS --safe #-}
module Notation.Double.Whiskering.Right where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Double.Base
open import Notation.Double.Composition
open import Notation.Reflexivity

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-sq : ℓ-sq-sig}
  (C : ℚuiver-on Ob ℓ-sq) (open ℚuiver-on C)
  ⦃ _ : Compω Quiverₕ ⦄ ⦃ _ : Reflω Quiverᵥ ⦄ where

  record 𝕎hisker-r : Typeω where -- TODO levels
    no-eta-equality
    infixr 24 _▷_
    field _▷_ : ∀{ℓw ℓx ℓy ℓz} {w : Ob ℓw} {x : Ob ℓx} {f : Hor w x}
                {y : Ob ℓy} {g : Ver w y} {h : Hor y x} (α : Sq f g refl h)
                {z : Ob ℓz} (k : Hor x z)
              → Sq (f ∙ k) g refl (h ∙ k)

open 𝕎hisker-r ⦃ ... ⦄ public

{-# DISPLAY 𝕎hisker-r._▷_ _ α k = α ▷ k #-}

-- TODO composition -> whiskering

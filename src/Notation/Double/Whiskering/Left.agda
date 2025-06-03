{-# OPTIONS --safe #-}
module Notation.Double.Whiskering.Left where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Double.Base
open import Notation.Double.Composition
open import Notation.Reflexivity

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-sq : ℓ-sq-sig}
  (C : ℚuiver-on Ob ℓ-sq) (open ℚuiver-on C)
  ⦃ _ : Compω Quiverₕ ⦄ ⦃ _ : Reflω Quiverᵥ ⦄ where

  record 𝕎hisker-l : Typeω where -- TODO levels
    no-eta-equality
    infixr 24 _◁_
    field _◁_ : ∀{ℓw ℓx ℓy ℓz} {w : Ob ℓw} {x : Ob ℓx} (f : Hor w x)
                {y : Ob ℓy} {g : Hor x y} {z : Ob ℓz} {h : Ver y z} {k : Hor x z}
              → Sq g refl h k
              → Sq (f ∙ g) refl h (f ∙ k)

open 𝕎hisker-l ⦃ ... ⦄ public

{-# DISPLAY 𝕎hisker-l._◁_ _ f α = f ◁ α #-}

-- TODO composition -> whiskering

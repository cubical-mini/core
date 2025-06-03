{-# OPTIONS --safe #-}
module Notation.Double.Composition where

open import Prim.Type

open import Notation.Base
open import Notation.Double.Base
open import Notation.Composition

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-sq : ℓ-sq-sig}
  (C : ℚuiver-on Ob ℓ-sq) (open ℚuiver-on C)
  (ℓw ℓx ℓy ℓz ℓu ℓv : Level)
  ⦃ _ : Compω Quiverₕ ⦄ ⦃ _ : Compω Quiverᵥ ⦄ where

  record ℂomp : Typeω where -- FIXME levels
    no-eta-equality
    infixl 90 _∙ₕ_ _∙ᵥ_
    field
      _∙ₕ_ : {w : Ob ℓw} {x : Ob ℓx} {f : Hor w x}
             {y : Ob ℓy} {g : Ver w y} {z : Ob ℓz} {h : Ver x z} {k : Hor y z} (α : Sq f g h k)
             {u : Ob ℓu} {l : Hor x u} {v : Ob ℓv} {m : Ver u v} {n : Hor z v} (β : Sq l h m n)
           → Sq (f ∙ l) g m (k ∙ n)
      _∙ᵥ_ : {w : Ob ℓw} {x : Ob ℓx} {f : Hor w x}
             {y : Ob ℓy} {g : Ver w y} {z : Ob ℓz} {h : Ver x z} {k : Hor y z} (α : Sq f g h k)
             {u : Ob ℓu} {l : Ver y u} {v : Ob ℓv} {m : Ver z v} {n : Hor u v} (β : Sq k l m n)
           → Sq f (g ∙ l) (h ∙ m) n

open ℂomp ⦃ ... ⦄ public

{-# DISPLAY ℂomp._∙ₕ_ _ α β = α ∙ₕ β #-}
{-# DISPLAY ℂomp._∙ᵥ_ _ α β = α ∙ᵥ β #-}

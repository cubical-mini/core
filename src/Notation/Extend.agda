{-# OPTIONS --safe #-}
module Notation.Extend where

open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) where
  record Extend : Typeω where
    no-eta-equality
    field
      extend : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy}
             → (h : Hom x y)
             → (∀{ℓt}(t : Ob ℓt) → Hom t x → Hom t y) -- gives composition
      extend-natural : ∀{ℓw ℓx ℓy ℓz} {w : Ob ℓw} {x : Ob ℓx} {y : Ob ℓy} {z : Ob ℓz}
                       (f : Hom w x) (g : Hom x y) (h : Hom y z)
                     → extend h w (extend g w f) ＝ extend (extend h x g) w f -- gives assoc

    -- is-equivω extend → Yoneda holds

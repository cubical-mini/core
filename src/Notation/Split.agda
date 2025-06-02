{-# OPTIONS --safe #-}
module Notation.Split where

open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Idempotent
open import Notation.Reflexivity
open import Notation.Strict

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  _retraction-of_ : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (r : Hom x y) (s : Hom y x) → Type (ℓ-hom ℓy ℓy)
  _retraction-of_ r s = s ∙ r ＝ refl
  {-# INLINE _retraction-of_ #-}

  _section-of_ : ∀{ℓx ℓy} {y : Ob ℓy} {x : Ob ℓx} (s : Hom y x) (r : Hom x y) → Type (ℓ-hom ℓy ℓy)
  _section-of_ s r = _retraction-of_ r s
  {-# INLINE _section-of_ #-}

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  record Split-pair {ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (s : Hom y x) (r : Hom x y) : Type (ℓ-hom ℓy ℓy) where
    no-eta-equality
    field split : r retraction-of s

open Split-pair ⦃ ... ⦄ public

{-# DISPLAY Split-pair.split _ = split #-}


-- module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
--   {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
--   {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} {s : Hom y x} {r : Hom x y}
--   ⦃ _ : Refl C ℓy ⦄ ⦃ _ : Comp C ℓy ℓx ℓy ⦄ ⦃ _ : Comp C ℓx ℓy ℓx  ⦄ ⦃ _ : Comp C ℓx ℓx ℓx ⦄
--   ⦃ _ : Split-pair C s r ⦄ where

--   Split→Idem : Idem C Strict (r ∙ s)
--   Split→Idem .idem = {!!} -- TODO need hom munging combinators

{-# OPTIONS --safe #-}
module Foundations.Representable where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Representable public

open import Foundations.Path.Groupoid.Base

module _ {ℓo ℓh : Level} {Ob : Type ℓo}
  (C : Small-quiver-on Ob ℓh) (open Small-quiver-on C)
  ⦃ _ : Refl (Enlarge C) lzero ⦄ ⦃ _ : Comp (Enlarge C) lzero lzero lzero ⦄ where

  Parametric : Type (ℓo l⊔ ℓh)
  Parametric = Weak-parametric C Strict

{-# DISPLAY Weak-parametric C Strict = Parametric C #-}

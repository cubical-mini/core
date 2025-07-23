{-# OPTIONS --safe #-}
module Foundations.Quiver.Interval.Category where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Interval.Base

open import Notation.Comp
open import Notation.Refl

instance
  𝐼-Refl : Refl 𝐼
  𝐼-Refl .refl {x = false} = oh
  𝐼-Refl .refl {x = true}  = oh

  𝐼-HComp : HComp 𝐼
  𝐼-HComp ._∙_ {x = false} _ _ = oh
  𝐼-HComp ._∙_ {x = true} {y = true} {z = true} _ _ = oh

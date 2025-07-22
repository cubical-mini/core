{-# OPTIONS --safe #-}
module Foundations.Quiver.Interval.Category where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Interval.Base

open import Notation.Comp
open import Notation.Refl

instance
  𝐼-Refl : Reflω 𝐼
  𝐼-Refl .refl {(false)} = oh
  𝐼-Refl .refl {(true)}  = oh

  𝐼-HComp : HCompω 𝐼
  𝐼-HComp ._∙_ {x = false} _ _ = oh
  𝐼-HComp ._∙_ {x = true} {y = true} {z = true} _ _ = oh

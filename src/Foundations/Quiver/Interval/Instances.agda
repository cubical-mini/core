{-# OPTIONS --safe #-}
module Foundations.Quiver.Interval.Instances where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete.Base
open import Foundations.Quiver.Interval.Base

open import Notation.Profunctor
open import Notation.Refl

instance
  𝐼-Refl : Refl 𝐼
  𝐼-Refl .refl {x = false} = oh
  𝐼-Refl .refl {x = true}  = oh

  𝐼-HProfunctor : HProfunctor 𝐼 𝐼 0 (λ x y → Disc (So (x implies y)))
  𝐼-HProfunctor .dimap {w = false} _ _ _ = oh
  𝐼-HProfunctor .dimap {w = true} {(true)} {(true)} _ q _ = q
  𝐼-HProfunctor .dimap-refl {x = false} {(y)} _ = oh
  𝐼-HProfunctor .dimap-refl {x = true} {(true)} _ = oh

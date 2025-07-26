{-# OPTIONS --safe #-}
module Foundations.Quiver.Interval.Instances where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete.Base
open import Foundations.Quiver.Interval.Base

open import Notation.Assoc.Left
open import Notation.Assoc.Right
open import Notation.Pull
open import Notation.Push
open import Notation.Refl

instance
  𝐼-Refl : Refl 𝐼
  𝐼-Refl .refl {x = false} = oh
  𝐼-Refl .refl {x = true}  = oh

  𝐼-Pull : {w : Bool} → HPull 𝐼 0 λ t → Disc (So (t implies w))
  𝐼-Pull .pull = _∙_
  𝐼-Pull {(false)} .pull-refl {y = false} _ = oh
  𝐼-Pull {(true)}  .pull-refl {y = false} _ = oh
  𝐼-Pull {(true)}  .pull-refl {y = true}  _ = oh

  𝐼-Push : {w : Bool} → HPush 𝐼 0 λ t → Disc (So (w implies t))
  𝐼-Push .push p q = q ∙ p
  𝐼-Push {(false)} .push-refl _ = oh
  𝐼-Push {(true)} .push-refl {x = true} _ = oh

  𝐼-RAssoc : {w : Bool} → RAssoc 𝐼 (λ t → Disc (So (w implies t)))
  𝐼-RAssoc .assoc-r = assoc

  𝐼-LAssoc : {w : Bool} → LAssoc 𝐼 (λ t → Disc (So (t implies w)))
  𝐼-LAssoc .assoc-l v p q = assoc p q v

{-# OVERLAPPING 𝐼-Refl 𝐼-Pull 𝐼-Push 𝐼-RAssoc 𝐼-LAssoc #-}

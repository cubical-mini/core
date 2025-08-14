{-# OPTIONS --safe #-}
module Foundations.Interval.Base where

open import Prim.Kan
open import Prim.Data.Bool
  using ( Bool ; false ; true ; _implies_
        ; So ; oh)
  public

open import Foundations.Base

-- \MiI
𝐼 : HQuiver-onω 0 (λ _ → Bool) λ _ _ → lzero
𝐼 .Quiver-onω.Het x y = So (x implies y)

infixl 90 _∙_
_∙_ : {x y z : Bool} → So (x implies y) → So (y implies z) → So (x implies z)
_∙_ {(false)} _ _ = oh
_∙_ {(true)} {(true)} _ q = q

assoc : ∀{w x y z} (p : So (w implies x)) (q : So (x implies y)) (r : So (y implies z))
      → p ∙ (q ∙ r) ＝ (p ∙ q) ∙ r
assoc {(false)} _ _ _ _ = oh
assoc {(true)} {(true)} _ q r _ = q ∙ r

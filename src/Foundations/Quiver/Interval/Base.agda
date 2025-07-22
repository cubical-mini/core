{-# OPTIONS --safe #-}
module Foundations.Quiver.Interval.Base where

open import Prim.Data.Bool
  using ( Bool ; false ; true ; _implies_
        ; So ; oh)
  public

open import Foundations.Quiver.Base

-- \MiI
𝐼 : HQuiver-onω 0 (λ _ → Bool) λ _ _ → lzero
𝐼 .Quiver-onω.Het x y = So (x implies y)

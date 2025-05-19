{-# OPTIONS --safe #-}
module Prim.Data.Unit where

open import Prim.Type

open import Agda.Builtin.Unit
  renaming (⊤ to ⊤ₜ)
  public

record ⊤ω : Typeω where
  instance constructor ttω

{-# OPTIONS --safe #-}
module Prim.Literals.FromNat where

open import Agda.Builtin.FromNat public
  using ()
  renaming ( Number  to From-ℕ
           ; fromNat to from-ℕ )

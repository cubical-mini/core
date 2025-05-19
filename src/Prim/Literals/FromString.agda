{-# OPTIONS --safe #-}
module Prim.Literals.FromString where

open import Agda.Builtin.FromString public
  using ()
  renaming ( IsString   to From-string
           ; fromString to from-string )

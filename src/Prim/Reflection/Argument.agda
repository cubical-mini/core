{-# OPTIONS --safe #-}
module Prim.Reflection.Argument where

open import Agda.Builtin.Reflection
  public
  using ( Visibility ; visible ; hidden ; instance′
        ; Relevance ; relevant ; irrelevant
        ; Quantity ; quantity-0 ; quantity-ω
        ; Modality ; modality
        ; arg-info
        ; Arg ; arg
        )
  renaming ( ArgInfo to Arg-info )

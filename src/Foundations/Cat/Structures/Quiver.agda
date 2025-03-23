{-# OPTIONS --safe #-}
module Control.Structures.Quiver where

open import Prim.Type

record Quiver o h : Type₊ (o ⊔ h) where
  constructor quiver
  no-eta-equality
  field
    Ob : Type o
    Hom : Ob → Ob → Type h

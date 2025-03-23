{-# OPTIONS --safe #-}
module Control.Structures.Quiver.Base where

open import Prim.Type

record Quiver o h : Type₊ (o ⊔ h) where
  constructor quiver
  no-eta-equality
  field
    ob : Type o
    hom : ob → ob → Type h

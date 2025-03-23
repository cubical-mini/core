```agda

module Cat.Base.Category where

open import Prim.Base
open import Prim.Data.Sigma
open import Prim.Pi hiding ( _∘_ )
open import Lib.Path.Base
open import Lib.Equiv.Base

open import Data.Semicategory.Base

open import Cat.Base.Axioms

record Category o h : Type₊ (o ⊔ h) where
  field
    base : Semicategory o h
    ax : ∀ x → has-identity base x

  open Semicategory base public
  module _ {x : Ob} where open has-identity (ax x) public

{-# OPTIONS --safe #-}
module Prelude where

open import Prim.Equiv    public
open import Prim.Glue     public
open import Prim.Interval public
open import Prim.Kan      public
open import Prim.Type     public

open import Prim.Literals.FromNat    public
open import Prim.Literals.FromNeg    public
open import Prim.Literals.FromString public
-- TODO add list literals


open import Notation.Adjoint           public
open import Notation.Associativity     public
open import Notation.Base              public
open import Notation.Composition       public
-- open import Notation.Coproduct.Binary  public -- TODO need displayed ids
-- open import Notation.Coproduct.Indexed public -- TODO need displayed ids
open import Notation.Displayed.Base public
open import Notation.Duality           public
-- open import Notation.Equivalence       public -- TODO as is-biinv
-- open import Notation.Identity      public -- NB: idemp equiv
open import Notation.Initial           public
-- open import Notation.Product.Binary    public -- TODO need displayed ids
-- open import Notation.Product.Indexed   public -- TODO need displayed ids
open import Notation.Reflexivity       public
open import Notation.Symmetry          public
open import Notation.Terminal          public
open import Notation.Unitality.Inner   public
open import Notation.Unitality.Outer   public

open import Foundations.Idempotent        public
open import Foundations.Invertible.Quasi       public
open import Foundations.Invertible.Retraction       public
open import Foundations.Invertible.Section       public
open import Foundations.Path.Groupoid public
open import Foundations.Pi.Category   public


-- Identity systems

-- Transport

-- HLevel

-- Univalence
-- should be stated as "equivalences form an identity system" for general cat

-- Size?
-- as ω-equivalence with a small quiver?

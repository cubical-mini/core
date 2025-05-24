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


-- open import Notation.Adjunction        public -- TODO 2-categorical?
open import Notation.Associativity     public
open import Notation.Base              public
open import Notation.Composition       public
-- open import Notation.Coproduct.Binary  public -- TODO need displayed ids
-- open import Notation.Coproduct.Indexed public -- TODO need displayed ids
open import Notation.Duality           public
-- open import Notation.Equivalence       public -- TODO
open import Notation.Idempotent        public
-- open import Notation.Identity      public -- NB: idemp equiv
open import Notation.Initial           public
-- open import Notation.Isomorphism       public -- TODO as strict adjunction?
-- open import Notation.Product.Binary    public -- TODO need displayed ids
-- open import Notation.Product.Indexed   public -- TODO need displayed ids
open import Notation.Reflexivity       public
-- open import Notation.Retract           public -- TODO
open import Notation.Retraction        public
open import Notation.Retraction.Strict public
open import Notation.Section           public
open import Notation.Section.Strict    public
open import Notation.Symmetry          public
open import Notation.Terminal          public
open import Notation.Unitality.Inner   public
open import Notation.Unitality.Outer   public

-- Function instances

-- Path instances

-- Identity systems

-- Transport

-- HLevel

-- Univalence
-- should be stated as "equivalences form an identity system" for general cat

-- Size?
-- as ω-equivalence with a small quiver

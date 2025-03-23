------------------------------------------------------------------------
-- The Agda standard library
--
-- Applicative functors
------------------------------------------------------------------------

-- Note that currently the applicative functor laws are not included
-- here.

{-# OPTIONS --cubical-compatible --safe #-}

module Control.Raw.Applicative where

open import Control.Functor as Fun using (RawFunctor)

open import Function.Base using (const; flip; _∘′_)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

private
  variable
    f g : Level
    A B C : Type f
------------------------------------------------------------------------
-- The type of raw applicatives

record RawApplicative (F : Type f → Type g) : Type (suc f ⊔ g) where
  infixl 4 _<*>_ _<*_ _*>_
  infixl 4 _⊛_ _<⊛_ _⊛>_
  infix  4 _⊗_
  field
    rawFunctor : RawFunctor F
    pure : A → F A
    _<*>_ : F (A → B) → F A → F B

  open RawFunctor rawFunctor public

  _<*_ : F A → F B → F A
  a <* b = const <$> a <*> b

  _*>_ : F A → F B → F B
  a *> b = flip const <$> a <*> b

  zipWith : (A → B → C) → F A → F B → F C
  zipWith f x y = f <$> x <*> y

  zip : F A → F B → F (A × B)
  zip = zipWith _,_

  -- Haskell-style alternative name for pure
  return : A → F A
  return = pure

module _ where

  open RawApplicative
  open RawFunctor

  -- Smart constructor
  mkRawApplicative :
    (F : Type f → Type g) →
    (pure : ∀ {A} → A → F A) →
    (app : ∀ {A B} → F (A → B) → F A → F B) →
    RawApplicative F
  mkRawApplicative F pure app .rawFunctor ._<$>_ = app ∘′ pure
  mkRawApplicative F pure app .pure = pure
  mkRawApplicative F pure app ._<*>_ = app

------------------------------------------------------------------------
-- The type of raw applicatives with a zero

record RawApplicativeZero (F : Type f → Type g) : Type (suc f ⊔ g) where
  field
    rawApplicative : RawApplicative F
    rawEmpty : RawEmpty F

  open RawApplicative rawApplicative public
  open RawEmpty rawEmpty public

------------------------------------------------------------------------
-- The type of raw alternative applicatives

record RawAlternative (F : Type f → Type g) : Type (suc f ⊔ g) where
  field
    rawApplicativeZero : RawApplicativeZero F
    rawChoice : RawChoice F

  open RawApplicativeZero rawApplicativeZero public
  open RawChoice rawChoice public

------------------------------------------------------------------------
-- The type of applicative morphisms

record Morphism {F₁ F₂ : Type f → Type g}
                (A₁ : RawApplicative F₁)
                (A₂ : RawApplicative F₂) : Type (suc f ⊔ g) where
  module A₁ = RawApplicative A₁
  module A₂ = RawApplicative A₂
  field
    functorMorphism : Fun.Morphism A₁.rawFunctor A₂.rawFunctor

  open Fun.Morphism functorMorphism public

  field
    op-pure : (x : A) → op (A₁.pure x) ≡ A₂.pure x
    op-<*>  : (f : F₁ (A → B)) (x : F₁ A) →
              op (f A₁.⊛ x) ≡ (op f A₂.⊛ op x)

  -- backwards compatibility: unicode variants
  op-⊛ = op-<*>

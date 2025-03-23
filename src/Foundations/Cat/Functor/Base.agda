{-# OPTIONS --safe #-}
module Control.Functor.Base where

open import Prim.Type
open import Prim.Interval

record Functor {ℓ ℓ'} (F : Type ℓ → Type ℓ') : Type (ℓ ₊ ⊔ ℓ') where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
    f-id : ∀ {A} (x : F A) → fmap (id {A = A}) x ≡ x
    f-hom : ∀ {A B C} (f : A → B) (g : B → C) {x : F A}
          → fmap (g ∘ f) x ≡ (fmap g ∘ fmap f) x

  syntax fmap f fa = f $ fa

  -- test : fFunctor F
  -- test .fFunctor.fmap f a = {!fmap!}
  -- test .fFunctor.f-id = {!!}
  -- --test .fFunctor.f-hom = {!!}

open Functor {{...}} public

instance
  Functor-Id : ∀ {ℓ} → Functor (id {A = Type ℓ})
  Functor-Id .fmap = id
  Functor-Id .f-id x = refl
  Functor-Id .f-hom f g = refl
{-# INCOHERENT Functor-Id #-}

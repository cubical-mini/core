{-# OPTIONS --safe #-}
module Notation.Comp.Pre where

open import Foundations.Quiver.Base

module _
  {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het ℓ-hom⁻}
  {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺} (C : Quiver-onω m n Ob⁻ Ob⁺ ℓ-het) (open Quiver-onω C)
  (A : HQuiver-onω m Ob⁻ ℓ-hom⁻) (open Quiver-onω A renaming (Het to Hom))
  where

  record LComp las lxs lys : Type
    ( ℓ-ob⁻ las ⊔ ℓ-ob⁻ lxs ⊔ ℓ-ob⁺ lys ⊔ ℓ-het las lys ⊔ ℓ-het lxs lys ⊔ ℓ-hom⁻ las lxs) where
    no-eta-equality
    infixl 240 _◁_
    field _◁_ : {a : Ob⁻ las} {x : Ob⁻ lxs} {y : Ob⁺ lys}
              → Hom a x → Het x y
              →           Het a y

  LCompω : Typeω
  LCompω = ∀{las lxs lys} → LComp las lxs lys

open LComp ⦃ ... ⦄ public
{-# DISPLAY LComp._◁_ _ f α = f ◁ α #-}


module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het ℓ-hom⁻}
  {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺} (C : Quiver-onω m n Ob⁻ Ob⁺ ℓ-het) (open Quiver-onω C)
  (A : HQuiver-onω m Ob⁻ ℓ-hom⁻) (open Quiver-onω A renaming (Het to Hom))
  {m′ n′ ℓ-obᵈ⁻ ℓ-obᵈ⁺ ℓ-hetᵈ ℓ-homᵈ⁻}
  {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺}
  (D : Quiver-onωᵈ Ob⁻ Ob⁺ Het m′ n′ Ob[_]⁻ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D)
  (A′ : HQuiver-onωᵈ Ob⁻ Hom m′ Ob[_]⁻ ℓ-homᵈ⁻) (open Quiver-onωᵈ A′ renaming (Het[_] to Hom[_]))
  ⦃ _ : LCompω C A ⦄ where

  record LCompᵈ las lxs lys lasᵈ lxsᵈ lysᵈ : Type
    ( ℓ-ob⁻ las ⊔ ℓ-ob⁻ lxs ⊔ ℓ-ob⁺ lys ⊔ ℓ-het lxs lys ⊔ ℓ-hom⁻ las lxs
    ⊔ ℓ-obᵈ⁻ las lasᵈ ⊔ ℓ-obᵈ⁻ lxs lxsᵈ ⊔ ℓ-obᵈ⁺ lys lysᵈ ⊔ ℓ-hetᵈ las lys lasᵈ lysᵈ
    ⊔ ℓ-hetᵈ lxs lys lxsᵈ lysᵈ ⊔ ℓ-homᵈ⁻ las lxs lasᵈ lxsᵈ) where
    no-eta-equality
    infixl 250 _◁ᵈ_
    field
      _◁ᵈ_ : {a : Ob⁻ las} {x : Ob⁻ lxs} {y : Ob⁺ lys}
             {f : Hom a x} {α : Het x y}
             {a′ : Ob[ a ]⁻ lasᵈ} {x′ : Ob[ x ]⁻ lxsᵈ} {y′ : Ob[ y ]⁺ lysᵈ}
           → Hom[ f ] a′ x′ → Het[ α ] x′ y′
           → Het[ f ◁ α  ] a′ y′

  LCompωᵈ : Typeω
  LCompωᵈ = ∀{las lxs lys lasᵈ lxsᵈ lysᵈ} → LCompᵈ las lxs lys lasᵈ lxsᵈ lysᵈ

open LCompᵈ ⦃ ... ⦄ public
{-# DISPLAY LCompᵈ._◁ᵈ_ _ f α = f ◁ᵈ α #-}

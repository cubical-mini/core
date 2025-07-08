{-# OPTIONS --safe #-}
module Notation.Comp.Double where

open import Foundations.Quiver.Base

module _
  {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het ℓ-hom⁻ ℓ-hom⁺} {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  (C : Quiver-onω m n Ob⁻ Ob⁺ ℓ-het) (open Quiver-onω C)
  (A : HQuiver-onω m Ob⁻ ℓ-hom⁻) (B : HQuiver-onω n Ob⁺ ℓ-hom⁺)
  where
  private module A = Quiver-onω A renaming (Het to Hom)
  private module B = Quiver-onω B renaming (Het to Hom)

  record DComp las lxs lys lbs : Type
    ( ℓ-ob⁻ las ⊔ ℓ-ob⁻ lxs ⊔ ℓ-ob⁺ lys ⊔ ℓ-ob⁺ lbs ⊔ ℓ-het las lbs
    ⊔ ℓ-het lxs lys ⊔ ℓ-hom⁻ las lxs ⊔ ℓ-hom⁺ lys lbs) where
    no-eta-equality
    field _∙∙_∙∙_ : {a : Ob⁻ las} {x : Ob⁻ lxs} {y : Ob⁺ lys} {b : Ob⁺ lbs}
                  → A.Hom a x → Het x y → B.Hom y b
                  →             Het a b

  DCompω : Typeω
  DCompω = ∀{las lxs lys lbs} → DComp las lxs lys lbs

open DComp ⦃ ... ⦄ public
{-# DISPLAY DComp._∙∙_∙∙_ _ f α g = f ∙∙ α ∙∙ g #-}


module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het ℓ-hom⁻ ℓ-hom⁺} {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  (C : Quiver-onω m n Ob⁻ Ob⁺ ℓ-het) (open Quiver-onω C)
  (A : HQuiver-onω m Ob⁻ ℓ-hom⁻)
  (B : HQuiver-onω n Ob⁺ ℓ-hom⁺)
  {m′ n′ ℓ-obᵈ⁻ ℓ-obᵈ⁺ ℓ-hetᵈ ℓ-homᵈ⁻ ℓ-homᵈ⁺}
  {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺}
  (D : Quiver-onωᵈ Ob⁻ Ob⁺ _ m′ n′ Ob[_]⁻ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D)
  (A′ : HQuiver-onωᵈ Ob⁻ _ m′ Ob[_]⁻ ℓ-homᵈ⁻)
  (B′ : HQuiver-onωᵈ Ob⁺ _ n′ Ob[_]⁺ ℓ-homᵈ⁺)
  ⦃ _ : DCompω C A B ⦄ where
  private module A where
    open Quiver-onω A renaming (Het to Hom) public
    open Quiver-onωᵈ A′ renaming (Het[_] to Hom[_]) public
  private module B where
    open Quiver-onω B renaming (Het to Hom) public
    open Quiver-onωᵈ B′ renaming (Het[_] to Hom[_]) public

  record DCompᵈ las lxs lys lbs lasᵈ lxsᵈ lysᵈ lbsᵈ : Type
    ( ℓ-ob⁻ las ⊔ ℓ-ob⁻ lxs ⊔ ℓ-ob⁺ lys ⊔ ℓ-ob⁺ lbs ⊔ ℓ-het lxs lys ⊔ ℓ-hom⁻ las lxs
    ⊔ ℓ-hom⁺ lys lbs ⊔ ℓ-obᵈ⁻ las lasᵈ ⊔ ℓ-obᵈ⁻ lxs lxsᵈ ⊔ ℓ-obᵈ⁺ lys lysᵈ
    ⊔ ℓ-obᵈ⁺ lbs lbsᵈ ⊔ ℓ-hetᵈ las lbs lasᵈ lbsᵈ ⊔ ℓ-hetᵈ lxs lys lxsᵈ lysᵈ
    ⊔ ℓ-homᵈ⁻ las lxs lasᵈ lxsᵈ ⊔ ℓ-homᵈ⁺ lys lbs lysᵈ lbsᵈ) where
    no-eta-equality
    field
      _∙∙_∙∙ᵈ_ : {a : Ob⁻ las} {x : Ob⁻ lxs} {y : Ob⁺ lys} {b : Ob⁺ lbs}
                 {f : A.Hom a x} {α : Het x y} {g : B.Hom y b}
                 {a′ : Ob[ a ]⁻ lasᵈ} {x′ : Ob[ x ]⁻ lxsᵈ} {y′ : Ob[ y ]⁺ lysᵈ} {b′ : Ob[ b ]⁺ lbsᵈ}
               → A.Hom[ f ] a′ x′ → Het[ α ] x′ y′ → B.Hom[ g ] y′ b′
               → Het[ f ∙∙ α ∙∙ g ] a′ b′

  DCompωᵈ : Typeω
  DCompωᵈ = ∀{las lxs lys lbs lasᵈ lxsᵈ lysᵈ lbsᵈ} → DCompᵈ las lxs lys lbs lasᵈ lxsᵈ lysᵈ lbsᵈ

open DCompᵈ ⦃ ... ⦄ public
{-# DISPLAY DCompᵈ._∙∙_∙∙ᵈ_ _ f α g = f ∙∙ α ∙∙ᵈ g #-}

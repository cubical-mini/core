{-# OPTIONS --safe #-}
module Control.Diagram.Coproduct.Binary where

open import Prim.Kan
open import Prim.Type

open import Control.Composition
open import Control.Structures.Quiver

module _ (C : Quiver) ⦃ _ : Comp C ⦄ where
  open Quiver C

  -- \(4 and \)4
  record is-coproduct ℓq {u v ℓs} {A : Ob u} {B : Ob v} {S : Ob ℓs} (ι₁ : Hom A S) (ι₂ : Hom B S) : Type (ob-lvl ℓq ⊔ hom-lvl u ℓq ⊔ hom-lvl v ℓq ⊔ hom-lvl ℓs ℓq) where
    no-eta-equality
    field
      ⁅_,_⁆ : {Q : Ob ℓq} (f : Hom A Q) (g : Hom B Q) → Hom S Q
      ⁅⁆∘ι₁ : {Q : Ob ℓq} {f : Hom A Q} {g : Hom B Q} → ⁅ f , g ⁆ ∘ ι₁ ≡ f
      ⁅⁆∘ι₂ : {Q : Ob ℓq} {f : Hom A Q} {g : Hom B Q} → ⁅ f , g ⁆ ∘ ι₂ ≡ g

      unique : {Q : Ob ℓq} {f : Hom A Q} {g : Hom B Q}
               {h : Hom S Q}
               (fs : h ∘ ι₁ ≡ f) (sn : h ∘ ι₂ ≡ g)
             → h ≡ ⁅ f , g ⁆

  record Coproduct {u v} (A : Ob u) (B : Ob v) (S : Ob (u ⊔ v)) : Typeω where
    no-eta-equality
    field
      ι₁  : Hom A S
      ι₂  : Hom B S
      has-is-coproduct : {ℓq : Level} → is-coproduct ℓq ι₁ ι₂

  -- \union 11
  record Binary-coproducts : Typeω where
    no-eta-equality
    infixr 70 _⨿_
    field
      _⨿_ : ∀ {u v} (A : Ob u) (B : Ob v) → Ob (u ⊔ v)
      has-coproduct : ∀ {u v} {A : Ob u} {B : Ob v} → Coproduct A B (A ⨿ B)


open is-coproduct ⦃ ... ⦄ public
  renaming (unique to ⁅⁆-unique)
open Coproduct ⦃ ... ⦄ public
  using (ι₁; ι₂)
open Binary-coproducts ⦃ ... ⦄ public
  using (_⨿_)

{-# DISPLAY is-coproduct.⁅_,_⁆ _ f g = ⁅ f , g ⁆ #-}
{-# DISPLAY is-coproduct.⁅⁆∘ι₁ _ = ⁅⁆∘ι₁ #-}
{-# DISPLAY is-coproduct.⁅⁆∘ι₂ _ = ⁅⁆∘ι₂ #-}
{-# DISPLAY is-coproduct.unique _ p q = ⁅⁆-unique p q #-}
{-# DISPLAY Coproduct.ι₁ _ = ι₁ #-}
{-# DISPLAY Coproduct.ι₂ _ = ι₂ #-}
{-# DISPLAY Binary-coproducts._⨿_ _ A B = A ⨿ B #-}

module _ {C : Quiver} ⦃ _ : Comp C ⦄ (let open Quiver C) where
  module _ ∀ {u v} {A : Ob u} {B : Ob v} where instance
    is-coproduct-helper : {ℓq : Level} {S : Ob (u ⊔ v)} ⦃ c : Coproduct C A B S ⦄ → is-coproduct C ℓq ι₁ ι₂
    is-coproduct-helper ⦃ c ⦄ = c .Coproduct.has-is-coproduct

    coproduct-helper : ⦃ c : Binary-coproducts C ⦄ → Coproduct C A B (A ⨿ B)
    coproduct-helper ⦃ c ⦄ = c .Binary-coproducts.has-coproduct

  infixr 71 _⨿→_
  _⨿→_ : ⦃ _ : Binary-coproducts C ⦄
       → {u v ℓs ℓq : Level} {A : Ob u} {B : Ob v} {S : Ob ℓs} {Q : Ob ℓq}
       → Hom S A → Hom Q B → Hom (S ⨿ Q) (A ⨿ B)
  f ⨿→ g = ⁅ f ∙ ι₁ , g ∙ ι₂ ⁆

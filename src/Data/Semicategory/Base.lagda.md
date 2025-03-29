```agda

module Data.Semicategory.Base where

open import Prim.Base
open import Prim.Data.Sigma

open import Lib.HLevel.Base

contr-comp : ∀ {ℓ} {A : Type ℓ} {a b c : A} → is-contr (a ＝ b) → is-contr (b ＝ c) → is-contr (a ＝ c)
contr-comp {ℓ} {A} {a} {b} {c} (p , h₁) (q , h₂) =
  let
    -- Create the center for a ＝ c by composing the centers of a ＝ b and b ＝ c
    center : a ＝ c
    center = p ∙ q
                   -- This is path composition: p ∙ q

    -- Now we need to show that every path r : a ＝ c is equal to our center
    paths : (r : a ＝ c) → center ＝ r
    paths r i j = hcomp (∂ j ∨ i) λ where
      k (j = i0) → p (k ∧ j)
      k (j = i1) → {!!}
      k (i = i1) → {!!}
      k (k = i0) → center j

    path : (r : a ＝ c) → p ∙ q ＝ r
    path r i j = {!!}
  in
    center , paths

unique-contraction-path : ∀ {ℓ} {A : Type ℓ} {a b c : A}
                        → is-contr (a ＝ b)
                        → is-contr (a ＝ c)
                        → is-contr (b ＝ c)
unique-contraction-path {a = a} {b} {c} (p , p-paths) (q , q-paths) =
  let
    -- Construct a canonical path from b to c
    b-to-c : b ＝ c
    b-to-c = sym p ∙ q

    -- Now we need to show that any path b ＝ c is homotopic to this one
    ba-contr : is-contr (b ＝ a)
    ba-contr = sym p , λ y → ap sym (p-paths (sym y))

    paths-bc : (i : I) → b ＝ c
    paths-bc = λ (i : I) → ba-contr .paths (sym p) i ∙ q-paths q i

    γ : is-contr (b ＝ c)
    γ = (λ i → paths-bc i i) , λ y → λ i → {!!}

  in γ

record Semicategory o h : Type₊ (o ⊔ h) where
  infixr 40 _∘_
  field
    Ob : Type o
    Hom : Ob → Ob → Type h
    _∘_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    comp-coh : ∀ {x y z} → (f : Hom x y) (g : Hom y z)
             → Σ h ∶ Hom x z , is-contr (fiber (_∘ f) h)

  assoc : ∀ {w x y z} (f : Hom w x) (g : Hom x y) (h : Hom y z)
        → (h ∘ g) ∘ f ＝ h ∘ (g ∘ f)
  assoc {w} {x} {y} {z} f g h =
    let
      -- Apply comp-coh to get composites with contractible fibers
      (α , (α-pt , p) , α-paths) = comp-coh g h   -- α is h ∘ g with contractible fiber
      (β , (β-pt , q) , β-paths) = comp-coh f g   -- β is g ∘ f with contractible fiber

      -- Now compose further
      (γ , (γ-pt , r) , γ-paths) = comp-coh f α   -- γ is α ∘ f = (h ∘ g) ∘ f with contractible fiber
      (δ , (δ-pt , s) , δ-paths) = comp-coh β h   -- δ is h ∘ β = h ∘ (g ∘ f) with contractible fiber
    in {!!}
      ∙ {!!}
      ∙ {!!}

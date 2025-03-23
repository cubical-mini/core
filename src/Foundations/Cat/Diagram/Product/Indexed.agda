{-# OPTIONS --safe #-}
module Control.Diagram.Product.Indexed where

open import Prim.Kan
open import Prim.Type

open import Control.Composition
open import Control.Structures.Quiver
open import Control.Underlying

module _ (C : Quiver) ⦃ _ : Comp C ⦄ {ℓi : Level} {Idx : Type ℓi} where
  open Quiver C

  record is-indexed-product ℓy {ℓp ℓf} {P : Ob ℓp} (F : Idx → Ob ℓf) (π : ∀ i → Hom P (F i)) : Type (ℓi ⊔ ob-lvl ℓy ⊔ hom-lvl ℓy ℓp ⊔ hom-lvl ℓy ℓf) where
    no-eta-equality
    field
      tuple   : {Y : Ob ℓy} → (∀ i → Hom Y (F i)) → Hom Y P
      commute : ∀{i} {Y : Ob ℓy} {f : ∀ i → Hom Y (F i)} → π i ∘ tuple f ≡ f i
      unique  : {Y : Ob ℓy} {h : Hom Y P} (f : ∀ i → Hom Y (F i)) → (∀ i → π i ∘ h ≡ f i) → h ≡ tuple f

  record Indexed-product {ℓf : Level} (F : Idx → Ob ℓf) (∏F : Ob (ℓi ⊔ ℓf)) : Typeω where
    no-eta-equality
    field
      π         : ∀ i → Hom ∏F (F i)
      has-is-ip : {ℓy : Level} → is-indexed-product ℓy F π

module _ (C : Quiver) ⦃ _ : Comp C ⦄ {ℓi : Level} (Idx : Type ℓi) where
  open Quiver C
  -- take care, it's not a greek letter pi, it's n-ary product symbol (\prod)
  record Indexed-products : Typeω where
    no-eta-equality
    field
      ∏      : {ℓf : Level} → (Idx → Ob ℓf) → Ob (ℓi ⊔ ℓf)
      has-ip : {ℓf : Level} {F : Idx → Ob ℓf} → Indexed-product C F (∏ F)

open is-indexed-product ⦃ ... ⦄ public
  renaming (tuple to ∏-tuple; commute to π-commute; unique to ∏-unique)
open Indexed-product ⦃ ... ⦄ public
  using (π)
open Indexed-products ⦃ ... ⦄ public
  using (∏)

{-# DISPLAY is-indexed-product.tuple _ F = ∏-tuple F #-}
{-# DISPLAY is-indexed-product.commute _ = π-commute #-}
{-# DISPLAY is-indexed-product.unique _ p q = ∏-unique p q #-}
{-# DISPLAY Indexed-product.π _ i = π i #-}
{-# DISPLAY Indexed-products.∏ _ F = ∏ F #-}

module _ {C : Quiver} (let open Quiver C) ⦃ _ : Comp C ⦄ {ℓi ℓf : Level} where
  ∏[_] : {Idx : Type ℓi} ⦃ _ : Indexed-products C Idx ⦄ → (Idx → Ob ℓf) → Ob (ℓi ⊔ ℓf)
  ∏[_] = ∏

  infixr 60 ∏-syntax
  ∏-syntax : ⦃ u : Underlying C ⦄ (X : Ob ℓi) ⦃ _ : Indexed-products C ⌞ X ⌟ ⦄
           → (⌞ X ⌟ → Ob ℓf) → Ob (ℓf ⊔ u .ℓ-und ℓi)
  ∏-syntax _ = ∏
  syntax ∏-syntax X (λ x → F) = ∏[ x ꞉ X ] F

  module _ {Idx : Type ℓi} {F : Idx → Ob ℓf} where instance
    is-ip-helper : {ℓy : Level} {ΠF : Ob (ℓi ⊔ ℓf)} ⦃ ip : Indexed-product C F ΠF ⦄ → is-indexed-product C ℓy F π
    is-ip-helper ⦃ ip ⦄ = ip .Indexed-product.has-is-ip

    ip-helper : ⦃ ip : Indexed-products C Idx ⦄ → Indexed-product C F ∏[ F ]
    ip-helper ⦃ ip ⦄ = ip .Indexed-products.has-ip

module _
  {C : Quiver} (let open Quiver C) ⦃ _ : Comp C ⦄
  {ℓi ℓf ℓg : Level} {Idx : Type ℓi} {F : Idx → Ob ℓf} {G : Idx → Ob ℓg} ⦃ _ : Indexed-products C Idx ⦄ where
    ∏→ : (α : (i : Idx) → Hom (F i) (G i)) → Hom ∏[ F ] ∏[ G ]
    ∏→ α = ∏-tuple λ i → π i ∙ α i

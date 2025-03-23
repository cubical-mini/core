{-# OPTIONS --safe #-}
module Control.Diagram.Coproduct.Indexed where

open import Prim.Kan
open import Prim.Type

open import Control.Composition
open import Control.Structures.Quiver
open import Control.Underlying

module _ (C : Quiver) ⦃ _ : Comp C ⦄ {ℓi : Level} {Idx : Type ℓi} where
  open Quiver C

  record is-indexed-coproduct ℓy {ℓs ℓf} {S : Ob ℓs} (F : Idx → Ob ℓf) (ι : ∀ i → Hom (F i) S) : Type (ℓi ⊔ ob-lvl ℓy ⊔ hom-lvl ℓs ℓy ⊔ hom-lvl ℓf ℓy) where
    no-eta-equality
    field
      match   : {Y : Ob ℓy} → (∀ i → Hom (F i) Y) → Hom S Y
      commute : ∀{i} {Y : Ob ℓy} {f : ∀ i → Hom (F i) Y} → match f ∘ ι i ≡ f i
      unique  : {Y : Ob ℓy} {h : Hom S Y} (f : ∀ i → Hom (F i) Y) → (∀ i → h ∘ ι i ≡ f i) → h ≡ match f

  record Indexed-coproduct {ℓf} (F : Idx → Ob ℓf) (∐F : Ob (ℓi ⊔ ℓf)) : Typeω where
    no-eta-equality
    field
      ι         : ∀ i → Hom (F i) ∐F
      has-is-ic : {ℓy : Level} → is-indexed-coproduct ℓy F ι

module _ (C : Quiver) ⦃ _ : Comp C ⦄ {ℓi : Level} (Idx : Type ℓi) where
  open Quiver C

  record Indexed-coproducts : Typeω where
    no-eta-equality
    field
      ∐      : {ℓf : Level} → (Idx → Ob ℓf) → Ob (ℓi ⊔ ℓf)
      has-ic : {ℓf : Level} {F : Idx → Ob ℓf} → Indexed-coproduct C F (∐ F)

open is-indexed-coproduct ⦃ ... ⦄ public
  renaming (match to ∐-match; commute to ι-commute; unique to ∐-unique)
open Indexed-coproduct ⦃ ... ⦄ public
  using (ι)
open Indexed-coproducts ⦃ ... ⦄ public
  using (∐)

{-# DISPLAY is-indexed-coproduct.match _ F = ∐-match F #-}
{-# DISPLAY is-indexed-coproduct.commute _ = ι-commute #-}
{-# DISPLAY is-indexed-coproduct.unique _ p q = ∐-unique p q #-}
{-# DISPLAY Indexed-coproduct.ι _ i = ι i #-}
{-# DISPLAY Indexed-coproducts.∐ _ F = ∐ F #-}

module _ {C : Quiver} (let open Quiver C) ⦃ _ : Comp C ⦄ {ℓi ℓf : Level} where
  ∐[_] : {Idx : Type ℓi} ⦃ _ : Indexed-coproducts C Idx ⦄ → (Idx → Ob ℓf) → Ob (ℓi ⊔ ℓf)
  ∐[_] = ∐

  infixr 60 ∐-syntax
  ∐-syntax : ⦃ u : Underlying C ⦄ (X : Ob ℓi) ⦃ _ : Indexed-coproducts C ⌞ X ⌟ ⦄
           → (⌞ X ⌟ → Ob ℓf) → Ob (ℓf ⊔ u .ℓ-und ℓi)
  ∐-syntax _ = ∐
  syntax ∐-syntax X (λ x → F) = ∐[ x ꞉ X ] F

  module _ {Idx : Type ℓi} {F : Idx → Ob ℓf} where instance
    is-ic-helper : {ℓy : Level} {∐F : Ob (ℓi ⊔ ℓf)} ⦃ ic : Indexed-coproduct C F ∐F ⦄ → is-indexed-coproduct C ℓy F ι
    is-ic-helper ⦃ ic ⦄ = ic .Indexed-coproduct.has-is-ic

    ic-helper : ⦃ ic : Indexed-coproducts C Idx ⦄ → Indexed-coproduct C F ∐[ F ]
    ic-helper ⦃ ic ⦄ = ic .Indexed-coproducts.has-ic

module _
  {C : Quiver} (let open Quiver C) ⦃ _ : Comp C ⦄
  {ℓi ℓf ℓg : Level} {Idx : Type ℓi} {F : Idx → Ob ℓf} {G : Idx → Ob ℓg} ⦃ _ : Indexed-coproducts C Idx ⦄ where
    ∐→ : (α : (i : Idx) → Hom (F i) (G i)) → Hom ∐[ F ] ∐[ G ]
    ∐→ α = ∐-match λ i → α i ∙ ι i

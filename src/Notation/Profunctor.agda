{-# OPTIONS --safe #-}
module Notation.Profunctor where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {ℓ-hom⁻}
  (A : HQuiver-onω m Ob⁻ ℓ-hom⁻) (let module A = Quiver-onω A renaming (Het to Hom))
  {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-hom⁺}
  (B : HQuiver-onω n Ob⁺ ℓ-hom⁺) (let module B = Quiver-onω B renaming (Het to Hom))
  k {ℓ-hetᶠ ℓ-hetᵍ} {ℓ-het : ℓ-sig 4 (m , n , k , k , _)}
  {F : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᶠ} {G : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᵍ}
  (α : ∀{lxs lys} (x : Ob⁻ lxs) (y : Ob⁺ lys) → Quiver-onω k (F x y) k (G x y) (ℓ-het lxs lys))
  ⦃ _ : Refl A ⦄ ⦃ _ : Refl B ⦄
  where
  private module α {lxs} {lys} x y = Quiver-onω (α {lxs} {lys} x y)

  record Profunctor : Typeω where
    no-eta-equality
    field
      dimap : ∀{lws lxs lys lzs lfs}
              {w : Ob⁻ lws} {x : Ob⁻ lxs} {y : Ob⁺ lys} {z : Ob⁺ lzs}
              (p : A.Hom w x) (q : B.Hom y z)
            → F x y lfs → G w z lfs
      dimap-refl : ∀{lxs lys lfs} {x : Ob⁻ lxs} {y : Ob⁺ lys}
                   {u : F x y lfs}
                 → α.Het x y u (dimap refl refl u)


    infix 300 _◁_▷_
    _◁_▷_ : ∀{lws lxs lys lzs lfs}
            {w : Ob⁻ lws} {x : Ob⁻ lxs} {y : Ob⁺ lys} {z : Ob⁺ lzs}
          → A.Hom w x → F x y lfs → B.Hom y z
          →             G w z lfs
    p ◁ α ▷ q = dimap p q α

open Profunctor ⦃ ... ⦄ public
{-# DISPLAY Profunctor.dimap _ p q u = dimap p q u #-}
{-# DISPLAY Profunctor.dimap-refl _ = dimap-refl #-}

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {ℓ-hom⁻}
  (A : HQuiver-onω m Ob⁻ ℓ-hom⁻) (let module A = Quiver-onω A renaming (Het to Hom))
  {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-hom⁺}
  (B : HQuiver-onω n Ob⁺ ℓ-hom⁺) (let module B = Quiver-onω B renaming (Het to Hom))
  k {ℓ-hetᶠ} {F : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᶠ}
  {ℓ-homα : ℓ-sig 4 (m , n , k , k , _)}
  (α : ∀{lxs lys} (x : Ob⁻ lxs) (y : Ob⁺ lys) → HQuiver-onω k (F x y) (ℓ-homα lxs lys)) where
  HProfunctor = Profunctor A B k α


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (let module C = Quiver-onω C renaming (Het to Hom))
  k {ℓ-homᶠ} {F : ob-sigᵈ² Ob Ob ℓ-homᶠ}
  {ℓ-homα : ℓ-sig 4 (m , m , k , k , _)}
  (α : ∀{lxs lys} (x : Ob lxs) (y : Ob lys) → HQuiver-onω k (F x y) (ℓ-homα lxs lys))
  ⦃ _ : Refl C ⦄ ⦃ _ : HProfunctor C C k α ⦄ where

  infix 300 _∙∙_∙∙_
  _∙∙_∙∙_ : ∀ {lws lxs lys lzs lfs}
            {w : Ob lws} {x : Ob lxs} {y : Ob lys} {z : Ob lzs}
          → C.Hom w x → F x y lfs → C.Hom y z
          →             F w z lfs
  p ∙∙ α ∙∙ q = p ◁ α ▷ q

{-# OPTIONS --safe #-}
module Notation.Profunctor where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-hom⁻ ℓ-hom⁺}
  {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  (A : HQuiver-onω m Ob⁻ ℓ-hom⁻) (let module A = Quiver-onω A renaming (Het to Hom))
  (B : HQuiver-onω n Ob⁺ ℓ-hom⁺) (let module B = Quiver-onω B renaming (Het to Hom))
  k {ℓ-hetᶠ ℓ-hetᵍ : Levels m → Levels n → ℓ-sig k}
  (F : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᶠ) (G : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᵍ) where

  record Profunctor lws lxs lys lzs lfs : Type
    ( ℓ-ob⁻ lws ⊔ ℓ-ob⁻ lxs ⊔ ℓ-ob⁺ lys ⊔ ℓ-ob⁺ lzs ⊔ ℓ-hom⁻ lws lxs
    ⊔ ℓ-hom⁺ lys lzs ⊔ ℓ-hetᶠ lxs lys lfs ⊔ ℓ-hetᵍ lws lzs lfs) where
    no-eta-equality
    field
      dimap : {w : Ob⁻ lws} {x : Ob⁻ lxs} {y : Ob⁺ lys} {z : Ob⁺ lzs}
              (p : A.Hom w x) (q : B.Hom y z)
            → F x y lfs → G w z lfs

    infix 300 _◁_▷_
    _◁_▷_ : {w : Ob⁻ lws} {x : Ob⁻ lxs} {y : Ob⁺ lys} {z : Ob⁺ lzs}
          → A.Hom w x → F x y lfs → B.Hom y z
          →             G w z lfs
    p ◁ α ▷ q = dimap p q α

  Profunctorω : Typeω
  Profunctorω = ∀{lws lxs lys lzs lfs} → Profunctor lws lxs lys lzs lfs

open Profunctor ⦃ ... ⦄ public
{-# DISPLAY Profunctor.dimap _ p q u = dimap p q u #-}


module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-hom⁻ ℓ-hom⁺}
  {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  (A : HQuiver-onω m Ob⁻ ℓ-hom⁻) (let module A = Quiver-onω A renaming (Het to Hom))
  (B : HQuiver-onω n Ob⁺ ℓ-hom⁺) (let module B = Quiver-onω B renaming (Het to Hom))
  {k} {ℓ-hetᶠ ℓ-hetᵍ : Levels m → Levels n → ℓ-sig k}
  {ℓ-hetʰ : Levels m → Levels n → ℓ-sig² k k}
  {F : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᶠ} {G : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᵍ}
  (H : ∀{lxs lys} (x : Ob⁻ lxs) (y : Ob⁺ lys) → Quiver-onω k k (F x y) (G x y) (ℓ-hetʰ lxs lys))
  ⦃ _ : Reflω A ⦄ ⦃ _ : Reflω B ⦄ ⦃ _ : Profunctorω A B k F G ⦄ where
  private module H {lxs} {lys} x y = Quiver-onω (H {lxs} {lys} x y)

  record Lawful-Profunctor lxs lys lfs : Type
    (ℓ-ob⁻ lxs ⊔ ℓ-ob⁺ lys ⊔ ℓ-hetᶠ lxs lys lfs ⊔ ℓ-hetʰ lxs lys lfs lfs) where
    no-eta-equality
    field
      dimap-refl : {x : Ob⁻ lxs} {y : Ob⁺ lys}
                   {u : F x y lfs}
                 → H.Het x y u (dimap refl refl u)

  Lawful-Profunctorω : Typeω
  Lawful-Profunctorω = ∀{lxs lys lfs} → Lawful-Profunctor lxs lys lfs

open Lawful-Profunctor ⦃ ... ⦄ public
{-# DISPLAY Lawful-Profunctor.dimap-refl _ = dimap-refl #-}


module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-hom⁻ ℓ-hom⁺}
  {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  (A : HQuiver-onω m Ob⁻ ℓ-hom⁻) (let module A = Quiver-onω A renaming (Het to Hom))
  (B : HQuiver-onω n Ob⁺ ℓ-hom⁺) (let module B = Quiver-onω B renaming (Het to Hom))
  k {ℓ-het : Levels m → Levels n → ℓ-sig k} (F : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-het) where

  HProfunctor = Profunctor A B k F F
  HProfunctorω = ∀{lws lxs lys lzs lfs} → HProfunctor lws lxs lys lzs lfs

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} (let module C = Quiver-onω C renaming (Het to Hom))
  k {ℓ-het : Levels m → Levels m → ℓ-sig k} {F : ob-sigᵈ² Ob Ob ℓ-het}
  {lws lxs lys lzs lfs} ⦃ _ : HProfunctor C C k F lws lxs lys lzs lfs ⦄ where

  infix 300 _∙∙_∙∙_
  _∙∙_∙∙_ : {w : Ob lws} {x : Ob lxs} {y : Ob lys} {z : Ob lzs}
          → C.Hom w x → F x y lfs → C.Hom y z
          →             F w z lfs
  p ∙∙ α ∙∙ q = p ◁ α ▷ q

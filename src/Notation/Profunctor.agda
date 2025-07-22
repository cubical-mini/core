{-# OPTIONS --safe #-}
module Notation.Profunctor where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {ma ℓ-oba⁻} {Oba⁻ : ob-sig ℓ-oba⁻} {na ℓ-oba⁺} {Oba⁺ : ob-sig ℓ-oba⁺}
  {ℓ-heta⁻} (A : Quiver-onω ma Oba⁻ na Oba⁺ ℓ-heta⁻) (let module A = Quiver-onω A)
  {mb ℓ-obb⁻} {Obb⁻ : ob-sig ℓ-obb⁻} {nb ℓ-obb⁺} {Obb⁺ : ob-sig ℓ-obb⁺}
  {ℓ-hetb⁻} (B : Quiver-onω mb Obb⁻ nb Obb⁺ ℓ-hetb⁻) (let module B = Quiver-onω B)
  k {ℓ-hetᶠ : ℓ-sig 3 (na , mb , k , _)} {ℓ-hetᵍ : ℓ-sig 3 (ma , nb , k , _)}
  (F : ob-sigᵈ² Oba⁺ Obb⁻ ℓ-hetᶠ) (G : ob-sigᵈ² Oba⁻ Obb⁺ ℓ-hetᵍ) where

  record Profunctor lws lxs lys lzs lfs : Type
    ( ℓ-oba⁻ lws ⊔ ℓ-oba⁺ lxs ⊔ ℓ-heta⁻ lws lxs ⊔ ℓ-obb⁻ lys ⊔ ℓ-obb⁺ lzs
    ⊔ ℓ-hetb⁻ lys lzs ⊔ ℓ-hetᶠ lxs lys lfs ⊔ ℓ-hetᵍ lws lzs lfs) where
    no-eta-equality
    field
      dimap : {w : Oba⁻ lws} {x : Oba⁺ lxs} {y : Obb⁻ lys} {z : Obb⁺ lzs}
              (p : A.Het w x) (q : B.Het y z)
            → F x y lfs → G w z lfs

    infix 300 _◁_▷_
    _◁_▷_ : {w : Oba⁻ lws} {x : Oba⁺ lxs} {y : Obb⁻ lys} {z : Obb⁺ lzs}
          → A.Het w x → F x y lfs → B.Het y z
          →             G w z lfs
    p ◁ α ▷ q = dimap p q α

  Profunctorω : Typeω
  Profunctorω = ∀{lws lxs lys lzs lfs} → Profunctor lws lxs lys lzs lfs

open Profunctor ⦃ ... ⦄ public
{-# DISPLAY Profunctor.dimap _ p q u = dimap p q u #-}

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {ℓ-hom⁻}
  (A : HQuiver-onω m Ob⁻ ℓ-hom⁻) (let module A = Quiver-onω A renaming (Het to Hom))
  {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-hom⁺}
  (B : HQuiver-onω n Ob⁺ ℓ-hom⁺) (let module B = Quiver-onω B renaming (Het to Hom))
  k where

  module _ {ℓ-hetᶠ} (F : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᶠ) where
    module _ {ℓ-hetᵍ} (G : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᵍ) where
      SProfunctor = Profunctor A B k F G
      SProfunctorω = ∀{lws lxs lys lzs lfs} → SProfunctor lws lxs lys lzs lfs

    HProfunctor = SProfunctor F
    HProfunctorω = ∀{lws lxs lys lzs lfs} → HProfunctor lws lxs lys lzs lfs


module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {ℓ-hom⁻}
  (A : HQuiver-onω m Ob⁻ ℓ-hom⁻) (let module A = Quiver-onω A renaming (Het to Hom))
  {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-hom⁺}
  (B : HQuiver-onω n Ob⁺ ℓ-hom⁺) (let module B = Quiver-onω B renaming (Het to Hom))
  {k ℓ-hetᶠ ℓ-hetᵍ} {ℓ-het : ℓ-sig 4 (m , n , k , k , _)}
  {F : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᶠ} {G : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᵍ}
  (α : ∀{lxs lys} (x : Ob⁻ lxs) (y : Ob⁺ lys) → Quiver-onω k (F x y) k (G x y) (ℓ-het lxs lys))
  ⦃ _ : Reflω A ⦄ ⦃ _ : Reflω B ⦄ ⦃ _ : SProfunctorω A B k F G ⦄ where
  private module α {lxs} {lys} x y = Quiver-onω (α {lxs} {lys} x y)

  record Lawful-Profunctor lxs lys lfs : Type
    (ℓ-ob⁻ lxs ⊔ ℓ-ob⁺ lys ⊔ ℓ-hetᶠ lxs lys lfs ⊔ ℓ-het lxs lys lfs lfs) where
    no-eta-equality
    field
      dimap-refl : {x : Ob⁻ lxs} {y : Ob⁺ lys}
                   {u : F x y lfs}
                 → α.Het x y u (dimap refl refl u)

  Lawful-Profunctorω : Typeω
  Lawful-Profunctorω = ∀{lxs lys lfs} → Lawful-Profunctor lxs lys lfs

open Lawful-Profunctor ⦃ ... ⦄ public
{-# DISPLAY Lawful-Profunctor.dimap-refl _ = dimap-refl #-}


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (let module C = Quiver-onω C renaming (Het to Hom))
  k {ℓ-het : ℓ-sig 3 (m , m , k , _)} {F : ob-sigᵈ² Ob Ob ℓ-het}
  {lws lxs lys lzs lfs} ⦃ _ : HProfunctor C C k F lws lxs lys lzs lfs ⦄ where

  infix 300 _∙∙_∙∙_
  _∙∙_∙∙_ : {w : Ob lws} {x : Ob lxs} {y : Ob lys} {z : Ob lzs}
          → C.Hom w x → F x y lfs → C.Hom y z
          →             F w z lfs
  p ∙∙ α ∙∙ q = p ◁ α ▷ q

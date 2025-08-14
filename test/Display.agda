{-# OPTIONS --safe #-}
module Display where

open import Foundations.Base
open import Foundations.Discrete as Discrete
open import Foundations.Lens.Extend
open import Foundations.Lens.Push
open import Foundations.Total
open import Foundations.Functions

open import Notation.Refl

-- Pointed structure

record Pointed {ℓ} (A : Type ℓ) : Type ℓ where
  constructor ∙
  field pt : A

instance
  Pointed-HPush : HPush Funs 0 (λ T → Disc (Pointed T))
  Pointed-HPush ._▷_ (∙ x) f = ∙ (f x)
  Pointed-HPush .push-refl = refl

Pointeds : HQuiver-onω 1 _ _
Pointeds = Σ̫[ Disp⁺ (λ T → Disc (Pointed T)) ]

Type∙ : (ℓ : Level) → Type (lsuc ℓ)
Type∙ ℓ = Quiver-onω.Out Pointeds (ℓ , _) ; {-# NOINLINE Type∙ #-}

Fun∙ : ∀{ℓa ℓb} → Type∙ ℓa → Type∙ ℓb → Type (ℓa ⊔ ℓb)
Fun∙ = Pointeds .Quiver-onω.Het ; {-# NOINLINE Fun∙ #-}


-- Magma structure

record Magma-on± {ℓa ℓb} (A : Type ℓa) (B : Type ℓb) : Type (ℓa ⊔ ℓb) where
  constructor mk-magma-on
  field _⋆_ : A → A → B

Magma-on : ∀{ℓ} (A : Type ℓ) → Type ℓ
Magma-on A = Magma-on± A A
{-# NOINLINE Magma-on #-}

instance
  Magma-Extend : Extend Funs 0 (λ A B _ → Disc (Magma-on± A B))
  Magma-Extend .extend-l p u .Magma-on±._⋆_ x y = p (x ⋆ y) where open Magma-on± u
  Magma-Extend .extend-r p v .Magma-on±._⋆_ x y = p x ⋆ p y where open Magma-on± v
  Magma-Extend .extend-refl = refl
  Magma-Extend .extend-coh = refl

Magmas : HQuiver-onω 1 _ _
Magmas = Σ̫[ Disp± (λ A B _ → Disc (Magma-on± A B)) ]

Magma : (ℓ : Level) → Type (lsuc ℓ)
Magma ℓ = Quiver-onω.Out Magmas (ℓ , _) ; {-# NOINLINE Magma #-}

Magma-Hom : ∀{ℓa ℓb} → Magma ℓa → Magma ℓb → Type (ℓa ⊔ ℓb)
Magma-Hom = Magmas .Quiver-onω.Het ; {-# NOINLINE Magma-Hom #-}


module Display-Structure {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} {f : A → B} where
  module _ {a : A} {b : B} {p : f a ＝ b} where private
    test : Fun∙ (A , ∙ a) (B , ∙ b)
    test .fst = f
    test .snd i = ∙ (p i)

  module _ {_⊕_ : A → A → A} {_⊗_ : B → B → B} {p : (x y : A) → f (x ⊕ y) ＝ (f x ⊗ f y)} where private
    test : Magma-Hom (A , mk-magma-on _⊕_) (B , mk-magma-on _⊗_)
    test .fst = f
    test .snd i .Magma-on±._⋆_ x y = p x y i

    -- ads : (t : Magma-Hom (A , mk-magma-on _⊕_) (B , mk-magma-on _⊗_)) → {!!}
    -- ads t = {!!}

-- module Hom-Induction {ℓa} where
--   module _ {A : Type ℓa} where
--     _∙₁_ : ∀{x y z : A} → x ＝ y → y ＝ z → x ＝ z
--     _∙₁_ p q = extend-l q p

--     _∙₂_ : {x y z : A} → x ＝ y → y ＝ z → x ＝ z
--     _∙₂_ = extend-r

  open Quiver-onω Magmas
  module Algebraic-Kek {M : Magma ℓa} where
     very-funny : (X : Magma ℓa) (h : X .fst → M .fst) (x y : X .fst) → M .fst
     very-funny X h = extend-l h (X .snd) .Magma-on±._⋆_

     -- if `to` and `from` are actual inverses you get something coherent
     transfer-structure : (X : Type ℓa) (to : X → M .fst) (from : M .fst → X)
                        → Magma-on X
     transfer-structure X to from .Magma-on±._⋆_ w z = from (extend-r to (M .snd) .Magma-on±._⋆_ w z)

{-# OPTIONS --safe --erased-cubical #-}
module Foundations.Quiver.Discrete.Instances where

open import Foundations.Path.Base
  renaming ( refl to reflₚ
           ; sym to symₚ
           ; _∙∙_∙∙_ to _∙∙_∙∙ₚ_
           ; _∙_ to _∙ₚ_ )
open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete.Base

open import Notation.Assoc.Left
open import Notation.Assoc.Right
open import Notation.Extend
open import Notation.Profunctor
open import Notation.Pull
open import Notation.Push
open import Notation.Refl
open import Notation.Sym

instance
  Disc-Refl : ∀{ℓ} {A : Type ℓ} → Refl (Disc A)
  Disc-Refl .refl {x} _ = x

  Disc-Sym : ∀{ℓ} {A : Type ℓ} → Sym (Disc A) λ x y → Disc (x ＝ y)
  Disc-Sym .sym p i = p (~ i)
  Disc-Sym .sym-invol = refl

module _ {ℓ} {A : I → Type ℓ} where instance
  PathP-Profunctor : HProfunctor (Disc (A i0)) (Disc (A i1)) 0 λ x y → Disc (Pathᴾ A x y)
  PathP-Profunctor .dimap p q h = p ∙∙ h ∙∙ₚ q
  PathP-Profunctor .dimap-refl {u} = ∙∙-filler refl u refl

module _ {ℓa} {A : Type ℓa} where instance
  Path-Push : {x : A} → HPush (Disc A) 0 λ y → Disc (x ＝ y)
  Path-Push .push q p = p ∙ q
  Path-Push .push-refl {u} = ∙-filler-l u refl

  Path-Pull : {y : A} → HPull (Disc A) 0 λ x → Disc (x ＝ y)
  Path-Pull .pull p q = p ∙ q
  Path-Pull .pull-refl {v} = sym (∙-filler-r refl v)

  Path-LAssoc : {y : A} → LAssoc (Disc A) λ x → Disc (x ＝ y)
  Path-LAssoc .assoc-l v p q i = ∙-filler-l p q (~ i) ∙ ∙-filler-r q v i

  Path-RAssoc : {x : A} → RAssoc (Disc A) λ y → Disc (x ＝ y)
  Path-RAssoc .assoc-r u p q i = ∙-filler-l u p (~ i) ∙ ∙-filler-r p q i

{-# OVERLAPPING
  Disc-Refl Disc-Sym
  PathP-Profunctor Path-Push Path-Pull
  Path-LAssoc Path-RAssoc
#-}


-- those are bad, use as a last resort

module _ {ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb} where instance

  Disc-Push : HPush (Disc A) 0 (λ t → Disc (B t))
  Disc-Push .push p = transp (λ i → B (p i)) i0
  Disc-Push .push-refl {x} {u} i = transp (λ j → B x) (~ i) u

  Disc-Pull : HPull (Disc A) 0 λ t → Disc (B t)
  Disc-Pull .pull p = transp (λ i → B (p (~ i))) i0
  Disc-Pull .pull-refl {y} {v} i = transp (λ j → B y) i v

{-# INCOHERENT Disc-Push Disc-Pull #-}

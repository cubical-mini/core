{-# OPTIONS --safe #-}
module Foundations.IdentitySystem.Base where

open import Prim.Kan
open import Prim.Type

module _ {ℓ ℓr} {A : Type ℓ} (R : A → A → Type ℓr) (rfl : ∀ a → R a a) where
  record is-identity-system : Type (ℓ l⊔ ℓr) where
    no-eta-equality
    field
      to-path : {x y : A} → R x y → x ＝ y
      to-path-over
        : {x y : A} (p : R x y)
        → Pathᴾ (λ i → R x (to-path p i)) (rfl x) p

-- TODO remove
-- open import Notation.Base
-- -- TODO naming
-- module _ {ℓo ℓh} {Ob : Type ℓo} (C : Small-quiver-on Ob ℓh) (open Small-quiver-on C) where
--   record Based : Type (ℓo l⊔ ℓh) where
--     no-eta-equality
--     field
--       centre : Ob
--       paths  : (x : Ob) → Hom centre x
--
--   record Fibred {ℓa} {A : Type ℓa} (f : A → Ob) (y : Ob) : Type (ℓa l⊔ ℓh) where
--     no-eta-equality
--     field
--       preimage : A
--       maps-to  : Hom y (f preimage)
--
-- open Based public
-- open Fibred public
--
-- open import Foundations.Path.Groupoid.Base
-- is-contr : ∀{ℓ} (A : Type ℓ) → Type ℓ
-- is-contr A = Based (Paths A)
-- {-# DISPLAY Based (Paths A) = is-contr A #-}
--
-- fibre : ∀{ℓa ℓb} {A : Type ℓa} {B : Type ℓb} (f : A → B) (y : B) → Type (ℓa l⊔ ℓb)
-- fibre {B} = Fibred (Paths B)
-- {-# DISPLAY Fibred (Paths B) = fibre {B = B} #-}
--
-- Singleton : ∀{ℓa} {A : Type ℓa} (x : A) → Type ℓa
-- Singleton = fibre (λ x → x)
--
-- open import Foundations.Path.Base
-- open import Prim.Interval
-- test : ∀{ℓa} {A : Type ℓa} (x : A) → is-contr (Singleton x)
-- test x .centre .preimage = x
-- test x .centre .maps-to = refl
-- test x .paths w i .preimage = w .maps-to i
-- test x .paths w i .maps-to j = w .maps-to (i ∧ j)
--
-- open import Notation.Reflexivity
-- open import Notation.Symmetry
-- open import Notation.Displayed.Base
-- module _ {ℓo ℓh ℓhᵈ} {Ob : Type ℓo}
--   (x : Ob)
--   (C : Small-quiver-on Ob ℓh) (open Small-quiver-on C)
--   (D : Small-quiver-onᵈ C (Hom x) ℓhᵈ) (open Small-quiver-onᵈ D)
--   ⦃ _ : Refl (Enlarge C) lzero ⦄
--   where
--   open import Prim.Data.Sigma
--
--   serious : Based (mk-small-quiver {Ob = Fibred C (λ x → x) x} λ u v → Σ (Hom (u .preimage) (v .preimage)) λ f → Hom[ f ] (u .maps-to) (v .maps-to))
--   serious .centre .preimage = x
--   serious .centre .maps-to = Notation.Reflexivity.refl
--   serious .paths w .fst = w .maps-to
--   serious .paths w .snd = {!!}
--
-- module Kekus {ℓ} {A : Type ℓ} {x : A} where
--
--   serious2 : is-contr (Singleton x)
--   serious2 = {!serious ? ? ? ⦃ ? ⦄!}

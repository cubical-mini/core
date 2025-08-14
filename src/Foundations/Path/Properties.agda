{-# OPTIONS --safe #-}
module Foundations.Path.Properties where

open import Foundations.Base
open import Foundations.Discrete.Base
open import Foundations.Path.Base

discrete-path-object : ∀{ℓ} (A : Type ℓ) → is-path-object (Disc A)
discrete-path-object _ .to-path p = p
discrete-path-object _ .to-path-over p i j = p (i ∧ j)

-- module _ {ℓo ℓh} {Ob : Type ℓo}
--   (C : HQuiver-onω 0 (λ _ → Ob) (λ _ _ → ℓh))
--   {k ℓ-obᶠ ℓ-homᶠ}
--   {F : Ob → ob-sig ℓ-obᶠ}
--   (α : (t : Ob) → HQuiver-onω k (F t) ℓ-homᶠ)
--   ⦃ _ : Refl C ⦄ (po : is-path-object C)
--   ⦃ _ : ∀{t} → Refl (α t) ⦄
--   where
--   private module α t = Quiver-onω (α t) renaming (Het to Hom)

--   module Default-Push2 where
--     Path-Object-Push : HPush C k α
--     Path-Object-Push .push p = coe0→1 (λ i → F (po .to-path p i) _)
--     Path-Object-Push .push-refl {lfs} {x} {u} =
--       let uu = po .to-path-over {x = x} refl
--           vv = from-pathᴾ uu
--       in {!!}
--       -- coe0→1 (λ i → α.Hom x u (coe1→i (λ j → {!F x lfs!}) (~ i) u)) {!!}
--       -- in subst (α.Hom _ u) (symₚ (transport-refl _) ∙
--       --   ap (λ φ → transport φ u) {x = refl} {y = ap (λ ψ → F ψ _) (po .to-path refl)} λ i → {!!}) refl

-- module _ {ℓo ℓh} {Ob : Type ℓo}
--   (C : HQuiver-onω 0 (λ _ → Ob) (λ _ _ → ℓh)) (open Quiver-onω C renaming (Het to Hom))
--   ⦃ _ : Refl C ⦄ (po : is-path-object C) where

--   module _ {k ℓ-obᶠ ℓ-homᶠ}
--     {F : {x y : Ob} → Hom x y → ob-sig ℓ-obᶠ}
--     (α : {x y : Ob} (p : Hom x y) → HQuiver-onω k (F p) ℓ-homᶠ)
--     ⦃ _ : {x y : Ob} {p : Hom x y} → Refl (α p) ⦄
--     where

--     Path-Object-Extend : Extend C k α
--     Path-Object-Extend .extend-l p =
--       coe0→1 (λ i → F (po .to-path-over p i) _)
--     Path-Object-Extend .extend-r p =
--       coe1→0 λ i → F (coe0→i (λ j → {!Hom _ _!}) i p) _
--     Path-Object-Extend .extend-refl = {!!}
--     Path-Object-Extend .extend-coh = {!!}

--   -- -- TODO reformulate using extend or push
--   -- J : ∀{ls} {x : Ob ls} {ℓ}
--   --     (P : (y : Ob ls) → Hom x y → Type ℓ)
--   --     ⦃ _ : Extend C 0 (λ {x = x′} {y = y′} p → Disc (P {!!} {!p!})) ⦄
--   --   → P x refl
--   --   → ∀ {b} s → P b s
--   -- J P pr s = {!!}
--   -- transport (λ i → P (po .to-path s i) (po .to-path-over s i)) pr

--   Jc : ∀{ℓ} (P : (x y : Ob) → Hom x y → Type ℓ)
--         ⦃ _ : Extend C 0 (λ {x = x′} {y = y′} p → Disc (P x′ y′ p)) ⦄
--         {x : Ob} (w : P x x refl)
--         {y : Ob} s → P x y s
--   Jc P {x} w s = extend-l s w -- J (P x)

--   -- J′ : ∀{ls} {x : Ob ls} {ℓ}
--   --     (P : (y : Ob ls) → Hom x y → Type ℓ)
--   --   → P x refl → ∀ {b} s → P b s
--   -- J′ {ls} {x} {ℓ} P pr {b} s =
--   --   let D : (x′ y′ : Ob ls) → Hom x′ y′ → Type (ℓ-ob ls ⊔ ℓ-hom ls ls ⊔ lsuc ℓ)
--   --       D x′ y′ q = (C : (z : Ob ls) → Hom x′ z → Type ℓ) → C x′ refl → C y′ q
--   --   in Jc D (λ _ w → w) s P pr

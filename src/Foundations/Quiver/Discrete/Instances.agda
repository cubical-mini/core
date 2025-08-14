{-# OPTIONS --safe #-}
module Foundations.Quiver.Discrete.Instances where

open import Foundations.Path.Base
  renaming ( refl to reflₚ
           ; sym  to symₚ )
open import Foundations.Path.Coe
open import Foundations.Path.Transport
open import Foundations.Path.Properties
open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete.Base
open import Foundations.Quiver.Lens.Extend.Base
open import Foundations.Quiver.Lens.Pull.Assoc
open import Foundations.Quiver.Lens.Pull.Base
open import Foundations.Quiver.Lens.Pull.Universal.Pullback
open import Foundations.Quiver.Lens.Push.Assoc
open import Foundations.Quiver.Lens.Push.Base
open import Foundations.Quiver.Lens.Push.Universal.Pushforward

open import Notation.Refl
open import Notation.Sym

-- Structural
module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  ⦃ _ : Refl C ⦄ where

  module Variadic-Extend where instance
    Disc-Extend-Const : ∀{ℓa} {A : Type ℓa} → Extend C 0 λ _ _ _ → Disc A
    Disc-Extend-Const .extend-l = _
    Disc-Extend-Const .extend-r = _
    Disc-Extend-Const .extend-refl = refl
    Disc-Extend-Const .extend-coh = refl
    {-# INCOHERENT Disc-Extend-Const #-}

    module _ {ℓf ℓg : ℓ-sig 2 (m , m , _)}
      {F : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → Type (ℓf lxs lys)}
      {G : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → Type (ℓg lxs lys)}
      ⦃ _ : Extend C 0 λ _ _ p → Disc (F p) ⦄ ⦃ _ : Extend C 0 λ _ _ p → Disc (G p) ⦄
      where instance
      Disc-Extend-× : Extend C 0 (λ _ _ p → Disc (F p ×ₜ G p))
      Disc-Extend-× .extend-l p (u , v) = extend-l p u , extend-l p v
      Disc-Extend-× .extend-r p (u , v) = extend-r p u , extend-r p v
      Disc-Extend-× .extend-refl {u = u , v} i = extend-refl {u = u} i , extend-refl {u = v} i
      Disc-Extend-× .extend-coh {u = u , v} i = extend-coh {u = u} i , extend-coh {u = v} i
    {-# OVERLAPS Disc-Extend-× #-}

  module Variadic-Push where instance
    Disc-Push-Const : ∀{ℓa} {A : Type ℓa} → Push C 0 (λ _ → Disc A)
    Disc-Push-Const ._▷_ = _
    Disc-Push-Const .push-refl = refl
    {-# INCOHERENT Disc-Push-Const #-}

    module _ {ℓf ℓg : ℓ-sig 1 (m , _)}
      {F : ∀{ls} → Ob ls → Type (ℓf ls)} {G : ∀{ls} → Ob ls → Type (ℓg ls)} where instance
      Disc-Push-× : ⦃ _ : HPush C 0 λ t → Disc (F t) ⦄ ⦃ _ : HPush C 0 λ t → Disc (G t) ⦄
                  → Push C 0 λ t → Disc (F t ×ₜ G t)
      Disc-Push-× ._▷_ (u , v) p = u ▷ p , v ▷ p
      Disc-Push-× .push-refl {u = u , v} i = push-refl {u = u} i , push-refl {u = v} i

      Disc-Push-→ : ⦃ _ : HPull C 0 λ t → Disc (F t) ⦄ ⦃ _ : HPush C 0 λ t → Disc (G t) ⦄
                  → Push C 0 λ t → Disc (F t → G t)
      Disc-Push-→ ._▷_ α p fy = α (p ◁ fy) ▷ p
      Disc-Push-→ .push-refl {u = α} i fx = push-refl {u = α (pull-refl {v = fx} (~ i))} i
    {-# OVERLAPS Disc-Push-× Disc-Push-→ #-}


  module Variadic-Pull where instance
    Disc-Pull-Const : ∀{ℓa} {A : Type ℓa} → Pull C 0 (λ _ → Disc A)
    Disc-Pull-Const ._◁_ = _
    Disc-Pull-Const .pull-refl = refl
    {-# INCOHERENT Disc-Pull-Const #-}

    module _ {ℓf ℓg : ℓ-sig 1 (m , _)}
      {F : ∀{ls} → Ob ls → Type (ℓf ls)} {G : ∀{ls} → Ob ls → Type (ℓg ls)} where instance
      Disc-Pull-× : ⦃ _ : HPull C 0 λ t → Disc (F t) ⦄ ⦃ _ : HPull C 0 λ t → Disc (G t) ⦄
                  → Pull C 0 λ t → Disc (F t ×ₜ G t)
      Disc-Pull-× ._◁_ p (u , v) = p ◁ u , p ◁ v
      Disc-Pull-× .pull-refl {v = u , v} i = pull-refl {v = u} i , pull-refl {v = v} i

      Disc-Pull-→ : ⦃ _ : HPush C 0 λ t → Disc (F t) ⦄ ⦃ _ : HPull C 0 λ t → Disc (G t) ⦄
                  → Pull C 0 λ t → Disc (F t → G t)
      Disc-Pull-→ ._◁_ p α fx = p ◁ α (fx ▷ p)
      Disc-Pull-→ .pull-refl {v = α} i fy = pull-refl {v = α (push-refl {u = fy} (~ i))} i
    {-# OVERLAPS Disc-Pull-× Disc-Pull-→ #-}


-- Path specific

module _ {ℓa} {A : Type ℓa} where instance
  Path-Push : {x : A} → HPush (Disc A) 0 λ y → Disc (x ＝ y)
  Path-Push ._▷_ = _∙_
  Path-Push .push-refl {u} = id-o u

  Path-Pull : {y : A} → HPull (Disc A) 0 λ x → Disc (x ＝ y)
  Path-Pull ._◁_ = _∙_
  Path-Pull .pull-refl {v} = id-i v

  Path-RAssoc : {x : A} → RAssoc (Path-Push {x = x}) Path-Push
  Path-RAssoc .RAssoc.assoc-r = assoc

  Path-LAssoc : {y : A} → LAssoc (Path-Pull {y = y}) Path-Pull
  Path-LAssoc .assoc-l v p q = assoc p q v

  Path-Pushforwards : {x : A} → Pushforwards (Path-Push {x = x})
  Path-Pushforwards {x} .push-univ {x = y} {y = z} p q (r , s) (t , u)
    =  sym s ∙ u
    ,ₚ to-pathᴾ (subst-path-right s _ ∙ assoc s _ _ ∙ ap (_∙ u) (path-inv (sym s)) ∙ sym (id-i u))

  Path-Pullbacks : {y : A} → Pullbacks (Path-Pull {y = y})
  Path-Pullbacks {y} .pull-univ {x} {y = z} p q (r , s) (t , u)
    =  s ∙ sym u
    ,ₚ to-pathᴾ ( subst-path-left s _ ∙ ap (_∙ s) (sym-∙ s _) ∙ sym (assoc u _ s)
                ∙ ap (u ∙_) (path-inv s) ∙ id-o u)

{-# OVERLAPPING
  Path-Push Path-Pull
  Path-RAssoc Path-LAssoc
  Path-Pushforwards Path-Pullbacks
#-}


-- Subst specific
-- these are bad, use as a last resort

module Default-Extend {ℓa} {A : Type ℓa} {k ℓ-obᶠ ℓ-homᶠ}
  {F : {x y : A} → x ＝ y → ob-sig ℓ-obᶠ}
  (α : (x y : A) (p : x ＝ y) → HQuiver-onω k (F p) ℓ-homᶠ)
  ⦃ _ : ∀{x y} {p : x ＝ y} → Refl (α x y p) ⦄ where instance
  private module α x y p = Quiver-onω (α x y p) renaming (Het to Hom)

  Disc-Extend : Extend (Disc A) k α
  Disc-Extend .extend-l p = coe0→1 λ i → F (λ j → p (i ∧ j)) _
  Disc-Extend .extend-r p = coe1→0 λ i → F (λ j → p (i ∨ j)) _
  Disc-Extend .extend-refl = refl
  Disc-Extend .extend-coh {u} = coe0→1 (λ i → α.Hom _ _ _ u (coe0→i _ i u)) refl
  {-# INCOHERENT Disc-Extend #-}

module _ {ℓa} {A : Type ℓa} {k ℓ-obᶠ ℓ-homᶠ}
  {F : A → ob-sig ℓ-obᶠ}
  (α : (t : A) → HQuiver-onω k (F t) ℓ-homᶠ)
  ⦃ _ : ∀{t} → Refl (α t) ⦄ where
  private module α t = Quiver-onω (α t) renaming (Het to Hom)

  module Default-Push where instance
    Disc-Push : HPush (Disc A) k α
    Disc-Push ._▷_ {lfs} u p = coe0→1 (λ i → F (p i) lfs) u
    Disc-Push .push-refl {u} = coe0→1 (λ i → α.Hom _ (coe0→i _ i u) u) refl

    Disc-RAssoc : RAssoc Disc-Push Path-Push
    Disc-RAssoc .assoc-r {z} u p q = subst (λ φ → α.Hom z (u ▷ (p ▷ q)) φ)
      (subst-comp (λ ψ → F ψ _) p q u) refl

    -- TODO
    -- Disc-Pushforwards : Pushforwards (Disc A) α
    -- Disc-Pushforwards .Pushforwards.hp = Disc-Push
    -- Disc-Pushforwards .push-univ p u (v₁ , q₁) (v₂ , q₂) = {!!} ,ₚ {!!}

    {-# INCOHERENT Disc-Push Disc-RAssoc #-}

  module Default-Pull where instance
    Disc-Pull : HPull (Disc A) k α
    Disc-Pull ._◁_ p = coe1→0 (λ i → F (p i) _)
    Disc-Pull .pull-refl {v} = coe0→1 (λ i → α.Hom _ v (coe0→i _ i v)) refl

    Disc-LAssoc : LAssoc Disc-Pull Path-Pull
    Disc-LAssoc .assoc-l {x} v p q = subst (λ φ → α.Hom x (p ◁ q ◁ v) φ)
      (sym ( ap (λ ψ → transport ψ v) (ap sym (ap-comp-∙ _ p q) ∙ sym-∙ _ _)
           ∙ transport-comp _ _ v))
      refl

    -- TODO
    -- Disc-Pullbacks : Pullbacks (Disc A) α
    -- Disc-Pullbacks .Pullbacks.hp = Disc-Pull
    -- Disc-Pullbacks .pull-univ p v (u₁ , q₁) (u₂ , q₂) = {!!}

    {-# INCOHERENT Disc-Pull Disc-LAssoc #-}

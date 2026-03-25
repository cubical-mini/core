{-# OPTIONS --safe #-}
module Foundations.Discrete.Instances where

open import Foundations.Base
open import Foundations.Cubical.Path.Base
  renaming ( refl to reflₚ
           ; sym  to symₚ )
open import Foundations.Cubical.Path.Coe
open import Foundations.Cubical.Path.Transport
open import Foundations.Cubical.Path.Properties
open import Foundations.Discrete.Base
open import Foundations.Lens.Extend.Base
open import Foundations.Lens.Pull.Assoc
open import Foundations.Lens.Pull.Base
open import Foundations.Lens.Pull.Back
open import Foundations.Lens.Push.Assoc
open import Foundations.Lens.Push.Base
open import Foundations.Lens.Push.Forward

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

      -- TODO
      -- Disc-Extend-→ : Extend C 0 (λ _ _ p → Disc (F p → G p))
      -- Disc-Extend-→ .extend-l p f u = extend-l p (f {!!})
      -- Disc-Extend-→ .extend-r p f v = extend-r p (f {!!})
      -- Disc-Extend-→ .extend-refl = {!!}
      -- Disc-Extend-→ .extend-coh = {!!}

    {-# OVERLAPS Disc-Extend-× #-}

  module Variadic-Push where instance
    Disc-HPush-Const : ∀{ℓa} {A : Type ℓa} → HPush C 0 (λ _ → Disc A)
    Disc-HPush-Const ._▷_ = _
    Disc-HPush-Const .push-refl = refl
    {-# INCOHERENT Disc-HPush-Const #-}

    module _ {ℓf ℓg : ℓ-sig 1 (m , _)}
      {F : ∀{ls} → Ob ls → Type (ℓf ls)} {G : ∀{ls} → Ob ls → Type (ℓg ls)} where instance
      Disc-HPush-× : ⦃ _ : HPush C 0 λ t → Disc (F t) ⦄ ⦃ _ : HPush C 0 λ t → Disc (G t) ⦄
                   → HPush C 0 λ t → Disc (F t ×ₜ G t)
      Disc-HPush-× ._▷_ (u , v) p = u ▷ p , v ▷ p
      Disc-HPush-× .push-refl {u = u , v} i = push-refl {u = u} i , push-refl {u = v} i

      Disc-HPush-→ : ⦃ _ : HPull C 0 λ t → Disc (F t) ⦄ ⦃ _ : HPush C 0 λ t → Disc (G t) ⦄
                   → HPush C 0 λ t → Disc (F t → G t)
      Disc-HPush-→ ._▷_ α p fy = α (p ◁ fy) ▷ p
      Disc-HPush-→ .push-refl {u = α} i fx = push-refl {u = α (pull-refl {v = fx} (~ i))} i
    {-# OVERLAPS Disc-HPush-× Disc-HPush-→ #-}


  module Variadic-Pull where instance
    Disc-HPull-Const : ∀{ℓa} {A : Type ℓa} → HPull C 0 (λ _ → Disc A)
    Disc-HPull-Const ._◁_ = _
    Disc-HPull-Const .pull-refl = refl
    {-# INCOHERENT Disc-HPull-Const #-}

    module _ {ℓf ℓg : ℓ-sig 1 (m , _)}
      {F : ∀{ls} → Ob ls → Type (ℓf ls)} {G : ∀{ls} → Ob ls → Type (ℓg ls)} where instance
      Disc-HPull-× : ⦃ _ : HPull C 0 λ t → Disc (F t) ⦄ ⦃ _ : HPull C 0 λ t → Disc (G t) ⦄
                   → HPull C 0 λ t → Disc (F t ×ₜ G t)
      Disc-HPull-× ._◁_ p (u , v) = p ◁ u , p ◁ v
      Disc-HPull-× .pull-refl {v = u , v} i = pull-refl {v = u} i , pull-refl {v = v} i

      Disc-HPull-→ : ⦃ _ : HPush C 0 λ t → Disc (F t) ⦄ ⦃ _ : HPull C 0 λ t → Disc (G t) ⦄
                   → HPull C 0 λ t → Disc (F t → G t)
      Disc-HPull-→ ._◁_ p α fx = p ◁ α (fx ▷ p)
      Disc-HPull-→ .pull-refl {v = α} i fy = pull-refl {v = α (push-refl {u = fy} (~ i))} i
    {-# OVERLAPS Disc-HPull-× Disc-HPull-→ #-}


-- Path specific

module _ {ℓa} {A : Type ℓa} where instance
  Path-HPush : {x : A} → HPush (Disc A) 0 λ y → Disc (x ＝ y)
  Path-HPush ._▷_ = _∙_
  Path-HPush .push-refl {u} = id-o u

  Path-HPull : {y : A} → HPull (Disc A) 0 λ x → Disc (x ＝ y)
  Path-HPull ._◁_ = _∙_
  Path-HPull .pull-refl {v} = sym (id-i v)

  Path-RAssoc : {x : A} → RAssoc (Path-HPush {x = x}) Path-HPush
  Path-RAssoc .RAssoc.assoc-r = assoc

  Path-LAssoc : {y : A} → LAssoc (Path-HPull {y = y}) Path-HPull
  Path-LAssoc .assoc-l v p q = assoc p q v

  Path-Pushforwards : {x : A} → UPush (Path-HPush {x = x})
  Path-Pushforwards {x} .push-univ {x = y} {y = z} p q (r , s)
    =  s
    ,ₚ to-pathᴾ (subst-path-right _ _ ∙ id-i _)

  Path-Pullbacks : {y : A} → UPull (Path-HPull {y = y})
  Path-Pullbacks {y} .pull-univ {x} {y = z} p q (r , s)
    =  sym s
    ,ₚ to-pathᴾ (subst-path-left _ _ ∙ id-o _)

{-# OVERLAPPING
  Path-HPush Path-HPull
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
    Disc-HPush : HPush (Disc A) k α
    Disc-HPush ._▷_ {lfs} u p = coe0→1 (λ i → F (p i) lfs) u
    Disc-HPush .push-refl {u} = coe0→1 (λ i → α.Hom _ (coe0→i _ i u) u) refl

    Disc-RAssoc : RAssoc Disc-HPush Path-HPush
    Disc-RAssoc .assoc-r {z} u p q = subst (λ φ → α.Hom z (u ▷ (p ▷ q)) φ)
      (subst-comp (λ ψ → F ψ _) p q u) refl

    -- TODO
    -- Disc-Pushforwards : UPush (Disc-Push)
    -- Disc-Pushforwards .push-univ p u (v , q) =  {!!} ,ₚ {!!}

    {-# INCOHERENT Disc-HPush Disc-RAssoc #-}

  module Default-Pull where instance
    Disc-HPull : HPull (Disc A) k α
    Disc-HPull ._◁_ p = coe1→0 (λ i → F (p i) _)
    Disc-HPull .pull-refl {v} = coe0→1 (λ i → α.Hom _ v (coe0→i _ i v)) refl

    Disc-LAssoc : LAssoc Disc-HPull Path-HPull
    Disc-LAssoc .assoc-l {x} v p q = subst (λ φ → α.Hom x (p ◁ q ◁ v) φ)
      (sym ( ap (λ ψ → transport ψ v) (ap sym (ap-comp-∙ _ p q) ∙ sym-∙ _ _)
           ∙ transport-comp _ _ v))
      refl

    -- TODO
    -- Disc-Pullbacks : UPull Disc-Pull
    -- Disc-Pullbacks .pull-univ p v (u , q) = {!!}

    {-# INCOHERENT Disc-HPull Disc-LAssoc #-}

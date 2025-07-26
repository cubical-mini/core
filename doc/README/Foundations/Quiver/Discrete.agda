{-# OPTIONS --safe #-}
module README.Foundations.Quiver.Discrete where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete

open import Notation.Assoc.Left
open import Notation.Assoc.Right
open import Notation.Extend
open import Notation.Pull
open import Notation.Push
open import Notation.Refl
open import Notation.Sym

-- any reflexive graph family over a discrete quiver
-- has extend/pull/push which commutes with path composition

module _ {ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb} {x y z : A} (p : x ＝ y) (q : y ＝ z) where

  module Test-Push where private
    open Default-Push (λ t → Disc (B t))

    ex₁ ex₂ : B x → B z
    ex₁ bx = bx ▷ (p ▷ q)
    ex₂ bx = bx ▷ p ▷ q

    observe : ex₁ ＝ ex₂
    observe = fun-ext λ bx → assoc-r bx p q

    -- this is much simpler but too specific
    _ : ex₁ ＝ ex₂
    _ = fun-ext (subst-comp B p q)

  module Test-Pull where private
    open Default-Pull (λ t → Disc (B t))

    ex₁ ex₂ : B z → B x
    ex₁ bz = (p ◁ q) ◁ bz
    ex₂ bz = p ◁ q ◁ bz

    observe : ex₂ ＝ ex₁
    observe = fun-ext λ bz → assoc-l bz p q


module Test-Extend {ℓa ℓb} {A : Type ℓa} {B : (x y : A) (p : x ＝ y) → Type ℓb} {x y z : A} (p : x ＝ y) (q : y ＝ z) where private
  open Default-Extend (λ r → Disc (B _ _ r))

  ex₁ : B x x refl → B x z (p ▷ q)
  ex₁ = extend-l (p ▷ q)

  ex₂ : B x x refl → B x z (p ▷ q)
  ex₂ bx = subst² (λ a b → B x a b) q (to-pathᴾ (subst-path-right p q)) (extend-l p bx)

  ex₃ : B z z refl → B x z (p ▷ q)
  ex₃ = extend-r (p ▷ q)

  ex₄ : B z z refl → B x z (p ▷ q)
  ex₄ bz = subst² (λ a b → B a z b) (sym p) (to-pathᴾ (subst-path-left q (sym p))) (extend-r q bz)

  -- TODO what is associativity for extend?
  -- should be related to the fact that J preserves path composition

  huh : (t : A) (φ : y ＝ t) → Type ℓb
  huh t φ = B x t (p ▷ φ)

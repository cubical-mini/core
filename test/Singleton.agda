module Singleton where

open import Prim.Type

open import Notation.Displayed.Total

open import Foundations.Singleton

module _ {ℓa ℓb} {A : Type ℓa} where private
  test : (c : A) → is-central c → is-contr A
  test c cent .carrier = c
  test c cent .structured = cent

  module _ {B : Type ℓb} (f : A → B) where
    is-equiv′ : Type (ℓa l⊔ ℓb)
    is-equiv′ = (y : B) → is-contr (fibre f y)

    -- `fibre` is displayed badly
    havefib : {y : B} → fibre f y → A
    havefib {y} fib =
      let uu = fib .carrier
          vv = fib .structured
      in uu

  -- is-contr (is-contr A) ?
  -- lel .carrier .carrier = {!!}
  -- lel .carrier .structured x = {!!}
  -- lel .structured w i .carrier = {!!}
  -- lel .structured w i .structured = {!!}

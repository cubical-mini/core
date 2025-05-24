{-# OPTIONS --safe #-}
module README.Foundations.Transport where

open import Prim.Kan
open import Prim.Interval
open import Prim.Type

open import Foundations.Transport.Base

-- FIXME
-- Observe the computational behaviour of `coe`!
-- module _ {ℓ} (A : I → Type ℓ) where
--   coei0→0 : (a : A i0) → coei→0 A i0 a ＝ a
--   coei0→0 _ = {!!} -- refl

--   coei1→0 : (a : A i1) → coei→0 A i1 a ＝ coe1→0 A a
--   coei1→0 _ = {!!} -- refl

--   coei0→1 : (a : A i0) → coei→1 A i0 a ＝ coe0→1 A a
--   coei0→1 _ = {!!} -- refl

--   coei1→1 : (a : A i1) → coei→1 A i1 a ＝ a
--   coei1→1 _ = {!!} -- refl

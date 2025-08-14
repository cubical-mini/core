{-# OPTIONS --safe #-}
module Foundations.Cubical.Path where

open import Foundations.Cubical.Path.Base public
  renaming ( refl to reflₚ
           ; sym  to symₚ )
open import Foundations.Cubical.Path.Properties public
  renaming ( id-o to id-oₚ
           ; id-i to id-iₚ
           ; assoc to assocₚ
           )
open import Foundations.Cubical.Path.Coe public
open import Foundations.Cubical.Path.Transport public

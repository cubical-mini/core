{-# OPTIONS --safe #-}
module Foundations.Path where

open import Foundations.Path.Base public
  renaming ( refl to reflₚ
           ; sym  to symₚ )
open import Foundations.Path.Properties public
  renaming ( id-o to id-oₚ
           ; id-i to id-iₚ
           ; assoc to assocₚ
           )
open import Foundations.Path.Coe public
open import Foundations.Path.Transport public

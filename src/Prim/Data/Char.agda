{-# OPTIONS --safe #-}
module Prim.Data.Char where

open import Agda.Builtin.Char public
  using ( Char )
  renaming
  -- testing
  ( primIsLower      to is-lower?
  ; primIsDigit      to is-digit?
  ; primIsAlpha      to is-alpha?
  ; primIsSpace      to is-space?
  ; primIsAscii      to is-ascii?
  ; primIsLatin1     to is-latin1?
  ; primIsPrint      to is-print?
  ; primIsHexDigit   to is-hex-digit?
  ; primCharEquality to _char=?_
  -- transforming
  ; primToUpper to to-upper
  ; primToLower to to-lower
  -- converting
  ; primCharToNat to char→ℕ
  ; primNatToChar to ℕ→char )

open import Agda.Builtin.Char.Properties public
  using ()
  renaming ( primCharToNatInjective to char→ℕ-injⁱ)

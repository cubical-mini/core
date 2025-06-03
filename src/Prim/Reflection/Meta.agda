{-# OPTIONS --safe #-}
module Prim.Reflection.Meta where

open import Prim.Data.Equality

open import Agda.Builtin.Reflection
  public
  using ( Meta
        ; Blocker
        )
  renaming ( primMetaEquality to _meta=?_
           ; primMetaLess     to _meta<?_
           ; primShowMeta     to show-meta
           ; primMetaToNat    to meta→ℕ

           ; blockerAny  to blocker-any
           ; blockerAll  to blocker-all
           ; blockerMeta to blocker-meta
           )

-- wtf agda?
private module M where primitive
  primMetaToNatInjective : ∀ x y → meta→ℕ x ＝ⁱ meta→ℕ y → x ＝ⁱ y

open M
  public
  renaming ( primMetaToNatInjective to meta→ℕ-injⁱ )

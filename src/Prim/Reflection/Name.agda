module Prim.Reflection.Name where

open import Prim.Data.Equality

open import Agda.Builtin.Reflection
  public
  using ( Name
        )
  renaming ( primQNameEquality  to _name=?_
           ; primQNameLess      to _name<?_
           ; primShowQName      to show-name
           ; primQNameFixity    to name→fixity
           ; primQNameToWord64s to name→words64
           )

-- wtf agda?
private module N where primitive
  primQNameToWord64sInjective : ∀ x y → name→words64 x ＝ⁱ name→words64 y → x ＝ⁱ y

open N
  public
  renaming ( primQNameToWord64sInjective to name→words64-injⁱ )

module Prim.Data.String where

open import Agda.Builtin.String public
  using ( String )
  renaming
    ( primStringAppend   to infixr 5 _++ₛ_
    ; primStringUncons   to uncons
    ; primStringToList   to string→list
    ; primStringFromList to list→string
    ; primShowChar       to show-char
    ; primStringEquality to infixl 5 _=ₛ_
    ; primShowString     to show-string
    ; primShowNat        to show-ℕ
    )

open import Agda.Builtin.String.Properties public
  using ()
  renaming
    ( primStringToListInjective   to string→list-injⁱ
    ; primStringFromListInjective to list→string-injⁱ
    )

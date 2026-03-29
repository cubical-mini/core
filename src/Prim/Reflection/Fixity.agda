module Prim.Reflection.Fixity where

open import Agda.Builtin.Reflection
  public
  using ( left-assoc ; right-assoc; non-assoc
        ; Precedence ; related ; unrelated
        ; Fixity ; fixity
        )
  renaming ( Associativity to Associativity′ )

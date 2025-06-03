{-# OPTIONS --safe #-}
module Prim.Reflection.Term where

open import Agda.Builtin.Reflection
  public
  using ( Term ; var ; con ; def ; lam ; pat-lam ; pi ; agda-sort
          ; lit ; unknown
        ; Sort ; set ; prop ; inf
        ; Pattern ; dot ; proj
        ; Clause ; clause ; absurd-clause
        ; Definition ; function ; data-type ; record-type ; data-cons
          ; axiom ; prim-fun
        )
  renaming ( propLit to prop-lit
           ; absurd  to absurd′
           ; Type    to Type′
           )

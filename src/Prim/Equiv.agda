{-# OPTIONS --safe #-}
module Prim.Equiv where

-- equivalence of types is builtin
open import Agda.Builtin.Cubical.Equiv public
  using (equiv-proof)
  renaming ( _≃_           to infix 10 _≃_
           ; isEquiv       to is-equiv
           ; equivFun      to equiv-forward
           ; equivProof    to equiv-proof-fast
           ; pathToisEquiv to =→is-equiv
           ; pathToEquiv   to =→≃
           )

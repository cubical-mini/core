{-# OPTIONS --safe #-}
module Prim.Equiv where

-- equivalence of types is builtin
open import Agda.Builtin.Cubical.Equiv public
  using ()
  renaming ( _≃_           to infix 1 _≃ₜ_
           ; equiv-proof   to equiv-proofₜ
           ; isEquiv       to is-equivₜ
           ; equivFun      to equiv-forwardₜ
           ; equivProof    to equiv-proof-fastₜ
           ; pathToisEquiv to =→is-equivₜ
           ; pathToEquiv   to =→≃ₜ
           )

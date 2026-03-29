module Prim.Data.Word where

open import Agda.Builtin.Word public
  using ( Word64 )
  renaming ( primWord64ToNat   to word64→ℕ
           ; primWord64FromNat to ℕ→word64 )

open import Agda.Builtin.Word.Properties public
  using ()
  renaming ( primWord64ToNatInjective to word64→ℕ-injⁱ)

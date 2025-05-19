{-# OPTIONS --safe #-}
module Prim.Reflection where

open import Agda.Builtin.Reflection public
  using ( TC ; bindTC ; returnTC ; catchTC ; commitTC
        ; blockTC ; quoteTC ; unquoteTC ; quoteωTC
        ; reduce ; normalise ; unify )
  renaming ( inferType to infer-type
           ; checkType to check-type
           ; extendContext to extend-context
           ; inContext to in-context
           ; freshName to fresh-name
           ; declareDef to declare-def
           ; declareData to declare-data
           ; defineData to define-data
           ; declarePostulate to declare-postulate
           ; defineFun to define-function
           ; getType to get-type
           ; getDefinition to get-definition
           ; getContext to get-context
           ; isMacro to is-macro?
           ; typeError to type-error
           ; formatErrorParts to format-error-parts
           ; debugPrint to debug-print
           ; withNormalisation to with-normalisation
           ; askNormalisation to ask-normalisation
           ; withReconstructed to with-reconstructed
           ; askReconstructed to ask-reconstructed
           ; withExpandLast to with-expand-last
           ; askExpandLast to ask-expand-last
           ; withReduceDefs to with-reduce-defs
           ; askReduceDefs to ask-reduce-defs
           ; noConstraints to no-constraints
           ; runSpeculative to run-speculative
           ; getInstances to get-instances
           ; solveInstanceConstraints to solve-instance-constraints
           ; blockOnMeta to block-on-meta
           ; workOnTypes to work-on-types
           )

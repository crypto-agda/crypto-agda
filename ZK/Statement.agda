{-# OPTIONS --without-K #-}

open import Data.ShapePolymorphism

module ZK.Statement where

-- The use of Agda irrelevance is an effort at modeling ZK.
-- * The witness is shape-polymorphic (marked with `☐`, but it is
--   called `..` internally) meaning that it cannot be
--   eliminated/inspect unless the whole expression is itself
--   shape-polymorphic.
-- * The second field holds a proof that the witness has the property
--   P. This field is irrelevant (marked with a `.`) meaning that not
--   only one cannot inspect the proof but any two proofs of the same
--   statement are considered equal.
record ZKStatement (A : Set) (P : (w : ☐ A) → Set) : Set where
  constructor _,_
  field
    witness-known   : ☐ A
    .proper-witness : P witness-known
open ZKStatement public

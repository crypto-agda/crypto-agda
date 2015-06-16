{-# OPTIONS --without-K #-}
open import FFI.JS      using (Number)
open import FFI.JS.BigI using (BigI)

module Crypto.JS.BigI.ZqZp.Params where

record Params : Set where
  field
    primality-test-probability-bound : Number
    min-bits-q min-bits-p            : Number
    qI pI gI                         : BigI

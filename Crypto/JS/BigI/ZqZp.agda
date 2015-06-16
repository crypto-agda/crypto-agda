{-# OPTIONS --without-K #-}
open import FFI.JS      using (JS!; _>>_)
open import FFI.JS.BigI using (BigI)
import      Crypto.JS.BigI.CyclicGroup as 𝔾
import      Crypto.JS.BigI.FiniteField as 𝔽
open import Crypto.JS.BigI.Checks
open import Crypto.JS.BigI.ZqZp.Params using (Params; module Params)

module Crypto.JS.BigI.ZqZp (params : Params) where

open Params params

checks! : JS!
checks! =
  check-pq-relation!      pI qI >>
  check-size! min-bits-q "q" qI >>
  check-size! min-bits-p "p" pI >>
  check-primality!       "q" qI primality-test-probability-bound >>
  check-primality!       "p" pI primality-test-probability-bound >>
  check-generator-group-order! gI qI pI

module ℤq = 𝔽 qI
  using (0#; 1#; _+_; _−_; _*_) -- ; _/_)
  renaming (𝔽 to ℤq; BigI▹𝔽 to BigI▹ℤq; repr to ℤq-repr)
module ℤp★ = 𝔾 pI
  using (_==_)
  renaming ( BigI▹𝔾 to BigI▹ℤp★; 𝔾 to ℤp★; _*_ to _·_
           ; _/_ to _·/_
           ; _^_ to _^I_ )

open ℤq  public
open ℤp★ public

g : ℤp★
g = BigI▹ℤp★ gI

_^_ : ℤp★ → ℤq → ℤp★
b ^ e = b ^I ℤq-repr e
-- -}

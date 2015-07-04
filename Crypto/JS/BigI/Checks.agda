{-# OPTIONS --without-K #-}
open import FFI.JS renaming (_*_ to _*N_)

open import FFI.JS.Check
open import FFI.JS.BigI as BigI using (BigI)
open import Crypto.JS.BigI.Params

module Crypto.JS.BigI.Checks where

check-size! : Number → String → BigI → JS!
check-size! min-bits name value =
  check! ("check size of " ++ name)
         (len ≥Number min-bits)
         (λ _ → name ++ " is not a necessarily a safe prime: "
             ++ BigI.toString value    ++ " has "
             ++ Number▹String len      ++ " bits which is less than "
             ++ Number▹String min-bits ++ " bits")
  module Check-size where
    len = BigI.byteLength value *N 8N

check-pq-relation! : (p q : BigI) → JS!
check-pq-relation! p q =
  -- I hit a bug of the JS backend when this block was a "where" block.
  -- With a "let" the computations gets duplicated (which is not too bad here).
  let
    open BigI
    p-1 = subtract p 1I
    r   = mod    p-1 q
    s   = divide p-1 q
  in
  check! ("check p and q relation p-1/q=" ++ BigI.toString s)
         (equals r 0I)
         (λ _ → "Not necessarily a safe group: (p-1) mod q != 0\np="
              ++ BigI.toString p
              ++ ", q=" ++ BigI.toString q)

check-primality! : (name : String) → BigI →
                   (primality-test-probability-bound : Number) → JS!
check-primality! name value primality-test-probability-bound =
  check! ("check primality of " ++ name)
         (BigI.isProbablePrime value primality-test-probability-bound)
         (λ _ → "Not a prime number: " ++ BigI.toString value)

check-generator-group-order! : (g q p : BigI) → JS!
check-generator-group-order! g q p =
  check! "check generator & group order"
        (BigI.equals (BigI.modPow g q p) BigI.1I)
        (λ _ → "Not a generator of a group of order q: modPow "
             ++ BigI.toString g ++ " " ++ BigI.toString q ++ " "
             ++ BigI.toString p)

check-params! : Params → JS!
check-params! gpq =
  check-pq-relation!      pI qI >>
  check-size! min-bits-q "q" qI >>
  check-size! min-bits-p "p" pI >>
  check-primality!       "q" qI primality-test-probability-bound >>
  check-primality!       "p" pI primality-test-probability-bound >>
  check-generator-group-order! gI qI pI
  module check-params where
    open module gpq = Params gpq

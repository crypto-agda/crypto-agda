{-# OPTIONS --without-K #-}
open import Type.Eq
open import FFI.JS using (Bool; trace-call; _++_)
open import FFI.JS.Check
  renaming (check      to check?)
--renaming (warn-check to check?)

open import FFI.JS.BigI
open import Data.List.Base using (List; foldr)
open import Data.Two hiding (_==_)
open import Relation.Binary.PropositionalEquality
open import Algebra.Raw
open import Algebra.Group

-- TODO carry on a primality proof of p
module Crypto.JS.BigI.CyclicGroup (p : BigI) where

abstract
  -- ℤp*
  𝔾 : Set
  𝔾 = BigI

  private
    mod-p : BigI → 𝔾
    mod-p x = mod x p

  -- There are two ways to go from BigI to 𝔾: check and mod-p
  -- Use check for untrusted input data and mod-p for internal
  -- computation.
  BigI▹𝔾 : BigI → 𝔾
  BigI▹𝔾 = -- trace-call "BigI▹𝔾 "
    λ x →
      (check? (x <I p)
         (λ _ → "Not below the modulus: p:" ++ toString p ++ " is less than x:" ++ toString x)
         (check? (x >I 0I)
            (λ _ → "Should be strictly positive: " ++ toString x ++ " <= 0") x))

  check-non-zero : 𝔾 → BigI
  check-non-zero = -- trace-call "check-non-zero "
    λ x → check? (x >I 0I) (λ _ → "Should be non zero") x

  repr : 𝔾 → BigI
  repr x = x

  1# : 𝔾
  1# = 1I

  1/_ : 𝔾 → 𝔾
  1/ x = modInv (check-non-zero x) p

  _^_ : 𝔾 → BigI → 𝔾
  x ^ y = modPow x y p

_*_ _/_ : 𝔾 → 𝔾 → 𝔾

x * y = mod-p (multiply (repr x) (repr y))
x / y = x * 1/ y

instance
  𝔾-Eq? : Eq? 𝔾
  𝔾-Eq? = record
    { _==_ = _=='_
    ; ≡⇒== = ≡⇒=='
    ; ==⇒≡ = ==⇒≡' }
    where
      _=='_ : 𝔾 → 𝔾 → 𝟚
      x ==' y = equals (repr x) (repr y)
      postulate
        ≡⇒==' : ∀ {x y} → x ≡ y → ✓ (x ==' y)
        ==⇒≡' : ∀ {x y} → ✓ (x ==' y) → x ≡ y

prod : List 𝔾 → 𝔾
prod = foldr _*_ 1#

mon-ops : Monoid-Ops 𝔾
mon-ops = _*_ , 1#

grp-ops : Group-Ops 𝔾
grp-ops = mon-ops , 1/_

postulate
  grp-struct : Group-Struct grp-ops

grp : Group 𝔾
grp = grp-ops , grp-struct

module grp = Group grp
-- -}
-- -}
-- -}
-- -}
-- -}

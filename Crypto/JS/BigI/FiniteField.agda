{-# OPTIONS --without-K #-}
open import Type.Eq
open import Data.Two hiding (_==_)
open import Relation.Binary.PropositionalEquality
open import FFI.JS using (Bool; trace-call; _++_)
open import FFI.JS.Check
  renaming (check      to check?)
--renaming (warn-check to check?)

open import FFI.JS.BigI
open import Data.List.Base using (List; foldr)
open import Algebra.Raw
open import Algebra.Field

-- TODO carry on a primality proof of q
module Crypto.JS.BigI.FiniteField (q : BigI) where

abstract
  -- ℤq
  𝔽 : Set
  𝔽 = BigI

  private
    mod-q : BigI → 𝔽
    mod-q x = mod x q

  -- There are two ways to go from BigI to 𝔽: BigI▹𝔽 and mod-q
  -- Use BigI▹𝔽 for untrusted input data and mod-q for internal
  -- computation.
  BigI▹𝔽 : BigI → 𝔽
  BigI▹𝔽 = -- trace-call "BigI▹𝔽 "
    λ x →
      (check? (x <I q)
         (λ _ → "Not below the modulus: q:" ++ toString q ++ " is less than x:" ++ toString x)
         (check? (x ≥I 0I)
            (λ _ → "Should be positive: " ++ toString x ++ " < 0") x))

  check-non-zero : 𝔽 → BigI
  check-non-zero = -- trace-call "check-non-zero "
    λ x → check? (x >I 0I) (λ _ → "Should be non zero") x

  repr : 𝔽 → BigI
  repr x = x

  0# 1# : 𝔽
  0# = 0I
  1# = 1I

  1/_ : 𝔽 → 𝔽
  1/ x = modInv (check-non-zero x) q

  _^_ : 𝔽 → BigI → 𝔽
  x ^ y = modPow x y q

_⊗_ : 𝔽 → BigI → 𝔽
x ⊗ y = mod-q (multiply (repr x) y)

_+_ _−_ _*_ _/_ : 𝔽 → 𝔽 → 𝔽

x + y = mod-q (add      (repr x) (repr y))
x − y = mod-q (subtract (repr x) (repr y))
x * y = x ⊗ repr y
x / y = x * 1/ y

0−_ : 𝔽 → 𝔽
0− x = mod-q (negate (repr x))

sum prod : List 𝔽 → 𝔽
sum  = foldr _+_ 0#
prod = foldr _*_ 1#

instance
  𝔽-Eq? : Eq? 𝔽
  𝔽-Eq? = record
    { _==_ = _=='_
    ; ≡⇒== = ≡⇒=='
    ; ==⇒≡ = ==⇒≡' }
    where
      _=='_ : 𝔽 → 𝔽 → 𝟚
      x ==' y = equals (repr x) (repr y)
      postulate
        ≡⇒==' : ∀ {x y} → x ≡ y → ✓ (x ==' y)
        ==⇒≡' : ∀ {x y} → ✓ (x ==' y) → x ≡ y

+-mon-ops : Monoid-Ops 𝔽
+-mon-ops = _+_ , 0#

+-grp-ops : Group-Ops 𝔽
+-grp-ops = +-mon-ops , 0−_

*-mon-ops : Monoid-Ops 𝔽
*-mon-ops = _*_ , 1#

*-grp-ops : Group-Ops 𝔽
*-grp-ops = *-mon-ops , 1/_

fld-ops : Field-Ops 𝔽
fld-ops = +-grp-ops , *-grp-ops

postulate
  fld-struct : Field-Struct fld-ops

fld : Field 𝔽
fld = fld-ops , fld-struct

module fld = Field fld

open fld using (+-grp) public
-- -}
-- -}
-- -}
-- -}

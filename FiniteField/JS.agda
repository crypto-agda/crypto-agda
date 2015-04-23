{-# OPTIONS --without-K #-}
open import Function.NP
open import FFI.JS using (Number; Bool; true; false; String; warn-check; check; trace-call; _++_)
open import FFI.JS.BigI
open import Data.List.Base hiding (sum; _++_)
{-
open import Algebra.Raw
open import Algebra.Field
-}

module FiniteField.JS (q : BigI) where

abstract
  ℤq : Set
  ℤq = BigI

  private
    mod-q : BigI → ℤq
    mod-q x = mod x q

  -- There is two ways to go from BigI to ℤq: check and mod-q
  -- Use check for untrusted input data and mod-q for internal
  -- computation.
  BigI▹ℤq : BigI → ℤq
  BigI▹ℤq = -- trace-call "BigI▹ℤq "
    λ x →
    mod-q
      (warn-check (x <I q)
         (λ _ → "Not below the modulus: " ++ toString q ++ " < " ++ toString x)
         (warn-check (x ≥I 0I)
            (λ _ → "Should be positive: " ++ toString x ++ " < 0") x))

  check-non-zero : ℤq → BigI
  check-non-zero = -- trace-call "check-non-zero "
    λ x → check (x >I 0I) (λ _ → "Should be non zero") x

  repr : ℤq → BigI
  repr x = x

  0# 1# : ℤq
  0# = 0I
  1# = 1I

  1/_ : Op₁ ℤq
  1/ x = modInv (check-non-zero x) q

  _^_ : Op₂ ℤq
  x ^ y = modPow (repr x) (repr y) q

_+_ _−_ _*_ _/_ : Op₂ ℤq

x + y = mod-q (add      (repr x) (repr y))
x − y = mod-q (subtract (repr x) (repr y))
x * y = mod-q (multiply (repr x) (repr y))
x / y = x * 1/ y

0−_ : Op₁ ℤq
0− x = mod-q (negate (repr x))

_==_ : (x y : ℤq) → Bool
x == y = equals (repr x) (repr y)

sum prod : List ℤq → ℤq
sum  = foldr _+_ 0#
prod = foldr _*_ 1#

{-
+-mon-ops : Monoid-Ops ℤq
+-mon-ops = _+_ , 0#

+-grp-ops : Group-Ops ℤq
+-grp-ops = +-mon-ops , 0−_

*-mon-ops : Monoid-Ops ℤq
*-mon-ops = _*_ , 1#

*-grp-ops : Group-Ops ℤq
*-grp-ops = *-mon-ops , 1/_

fld-ops : Field-Ops ℤq
fld-ops = +-grp-ops , *-grp-ops

postulate
  fld-struct : Field-Struct fld-ops

fld : Field ℤq
fld = fld-ops , fld-struct
-- -}
-- -}
-- -}
-- -}
-- -}

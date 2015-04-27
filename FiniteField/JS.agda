{-# OPTIONS --without-K #-}
open import Function.NP
open import FFI.JS using (𝟙; Number; Bool; true; false; String; warn-check; check; trace-call; _++_)
open import FFI.JS.BigI
open import Data.List.Base hiding (sum; _++_)
{-
open import Algebra.Raw
open import Algebra.Field
-}

module FiniteField.JS (q : BigI) where

abstract
  𝔽 : Set
  𝔽 = BigI

  private
    mod-q : BigI → 𝔽
    mod-q x = mod x q

    check' : {A : Set}(pred : Bool)(errmsg : 𝟙 → String)(input : A) → A
    -- check' = warn-check
    check' = check

  -- There is two ways to go from BigI to ℤq: check and mod-q
  -- Use check for untrusted input data and mod-q for internal
  -- computation.
  fromBigI : BigI → 𝔽
  fromBigI = -- trace-call "BigI▹ℤq "
    λ x →
      (check' (x <I q)
         (λ _ → "Not below the modulus: q:" ++ toString q ++ " is less than x:" ++ toString x)
         (check' (x ≥I 0I)
            (λ _ → "Should be positive: " ++ toString x ++ " < 0") x))

  check-non-zero : 𝔽 → BigI
  check-non-zero = -- trace-call "check-non-zero "
    λ x → check (x >I 0I) (λ _ → "Should be non zero") x

  repr : 𝔽 → BigI
  repr x = x

  0# 1# : 𝔽
  0# = 0I
  1# = 1I

  1/_ : Op₁ 𝔽
  1/ x = modInv (check-non-zero x) q

  _^_ : Op₂ 𝔽
  x ^ y = modPow (repr x) (repr y) q

_+_ _−_ _*_ _/_ : Op₂ 𝔽

x + y = mod-q (add      (repr x) (repr y))
x − y = mod-q (subtract (repr x) (repr y))
x * y = mod-q (multiply (repr x) (repr y))
x / y = x * 1/ y

0−_ : Op₁ 𝔽
0− x = mod-q (negate (repr x))

_==_ : (x y : 𝔽) → Bool
x == y = equals (repr x) (repr y)

sum prod : List 𝔽 → 𝔽
sum  = foldr _+_ 0#
prod = foldr _*_ 1#

{-
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
-- -}
-- -}
-- -}
-- -}
-- -}

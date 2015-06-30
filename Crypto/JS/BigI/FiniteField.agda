{-# OPTIONS --without-K #-}
open import Type.Eq
open import Data.Two hiding (_==_)
open import Relation.Binary.PropositionalEquality
open import FFI.JS using (JS[_]; _++_; return; _>>_)
open import FFI.JS.Check
  using    (check!)
  renaming (check      to check?)
--renaming (warn-check to check?)

open import FFI.JS.BigI
open import Data.List.Base using (List; foldr)
open import Algebra.Raw
open import Algebra.Field

-- TODO carry on a primality proof of q
module Crypto.JS.BigI.FiniteField (q : BigI) where

abstract
  ℤ[_] : Set
  ℤ[_] = BigI

  private
    ℤq : Set
    ℤq = ℤ[_]

    mod-q : BigI → ℤq
    mod-q x = mod x q

  -- There are two ways to go from BigI to ℤq: BigI▹ℤ[ q ] and mod-q
  -- Use BigI▹ℤ[ q ] for untrusted input data and mod-q for internal
  -- computation.
  BigI▹ℤ[_] : BigI → JS[ ℤq ]
  BigI▹ℤ[_] x =
  -- Console.log "BigI▹ℤ[_]"
    check! "below the modulus" (x <I q)
           (λ _ → "Not below the modulus: q:" ++ toString q ++
                  " is less than x:" ++ toString x) >>
    check! "positivity" (x ≥I 0I)
           (λ _ → "Should be positive: " ++ toString x ++ " < 0") >>
    return x

  check-non-zero : ℤq → BigI
  check-non-zero = -- trace-call "check-non-zero "
    λ x → check? (x >I 0I) (λ _ → "Should be non zero") x

  repr : ℤq → BigI
  repr x = x

  0# 1# : ℤq
  0# = 0I
  1# = 1I

  -- One could choose here to return a dummy value when 0 is given.
  -- Instead we throw an exception which in some circumstances could
  -- be bad if the runtime semantics is too eager.
  1/_ : ℤq → ℤq
  1/ x = modInv (check-non-zero x) q

  _^_ : ℤq → BigI → ℤq
  x ^ y = modPow x y q

_⊗_ : ℤq → BigI → ℤq
x ⊗ y = mod-q (multiply (repr x) y)

_+_ _−_ _*_ _/_ : ℤq → ℤq → ℤq

x + y = mod-q (add      (repr x) (repr y))
x − y = mod-q (subtract (repr x) (repr y))
x * y = x ⊗ repr y
x / y = x * 1/ y

0−_ : ℤq → ℤq
0− x = mod-q (negate (repr x))

sum prod : List ℤq → ℤq
sum  = foldr _+_ 0#
prod = foldr _*_ 1#

instance
  ℤ[_]-Eq? : Eq? ℤq
  ℤ[_]-Eq? = record
    { _==_ = _=='_
    ; ≡⇒== = ≡⇒=='
    ; ==⇒≡ = ==⇒≡' }
    where
      _=='_ : ℤq → ℤq → 𝟚
      x ==' y = equals (repr x) (repr y)
      postulate
        ≡⇒==' : ∀ {x y} → x ≡ y → ✓ (x ==' y)
        ==⇒≡' : ∀ {x y} → ✓ (x ==' y) → x ≡ y

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

module fld = Field fld

open fld using (+-grp) public
-- -}
-- -}
-- -}
-- -}

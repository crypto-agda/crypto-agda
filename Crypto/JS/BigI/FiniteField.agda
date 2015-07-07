{-# OPTIONS --without-K #-}
open import Type.Eq using (_==_; Eq?; ≡⇒==; ==⇒≡)
open import Data.Two.Base using (𝟚; ✓)
open import Relation.Binary.PropositionalEquality.Base using (_≡_; refl; ap)
open import FFI.JS using (JS[_]; _++_; return; _>>_)
open import FFI.JS.Check
  using    (check!)
--renaming (check      to check?)
  renaming (warn-check to check?)

open import FFI.JS.BigI
open import Data.List.Base using (List; foldr)
open import Algebra.Raw
open import Algebra.Group
open import Algebra.Group.Homomorphism
open import Algebra.Field

-- TODO carry on a primality proof of q
module Crypto.JS.BigI.FiniteField (q : BigI) where

-- The constructor mk is not exported.
private
  module Internals where
    data ℤ[_] : Set where
      mk : BigI → ℤ[_]

    mk-inj : ∀ {x y : BigI} → ℤ[_].mk x ≡ mk y → x ≡ y
    mk-inj refl = refl

open Internals public using (ℤ[_])
open Internals

ℤq : Set
ℤq = ℤ[_]

private
  mod-q : BigI → ℤq
  mod-q x = mk (mod x q)

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
  return (mk x)

check-non-zero : ℤq → BigI
check-non-zero (mk x) = -- trace-call "check-non-zero "
  check? (x >I 0I) (λ _ → "Should be non zero") x

ℤ[_]▹BigI : ℤq → BigI
ℤ[_]▹BigI (mk x) = x

0# 1# : ℤq
0# = mk 0I
1# = mk 1I

-- One could choose here to return a dummy value when 0 is given.
-- Instead we throw an exception which in some circumstances could
-- be bad if the runtime semantics is too eager.
1/_ : ℤq → ℤq
1/ x = mk (modInv (check-non-zero x) q)

_^I_ : ℤq → BigI → ℤq
mk x ^I y = mk (modPow x y q)

ℤq▹BigI = ℤ[_]▹BigI
BigI▹ℤq = BigI▹ℤ[_]

_⊗I_ : ℤq → BigI → ℤq
x ⊗I y = mod-q (multiply (ℤq▹BigI x) y)

_+_ _−_ _*_ _/_ : ℤq → ℤq → ℤq

x + y = mod-q (add      (ℤq▹BigI x) (ℤq▹BigI y))
x − y = mod-q (subtract (ℤq▹BigI x) (ℤq▹BigI y))
x * y = x ⊗I ℤq▹BigI y
x / y = x * 1/ y

*-def : _*_ ≡ (λ x y → x ⊗I ℤq▹BigI y)
*-def = refl

0−_ : ℤq → ℤq
0− x = mod-q (negate (ℤq▹BigI x))

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
      mk x ==' mk y = x == y
      ≡⇒==' : ∀ {x y} → x ≡ y → ✓ (x ==' y)
      ≡⇒==' {mk x} {mk y} p = ≡⇒== (mk-inj p)
      ==⇒≡' : ∀ {x y} → ✓ (x ==' y) → x ≡ y
      ==⇒≡' {mk x} {mk y} p = ap mk (==⇒≡ p)

ℤq-Eq?  = ℤ[_]-Eq?

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

postulate fld-struct : Field-Struct fld-ops

fld : Field ℤq
fld = fld-ops , fld-struct

module fld = Field fld

-- open fld using (+-grp) public

ℤ[_]+-grp : Group ℤq
ℤ[_]+-grp = fld.+-grp

ℤq+-grp : Group ℤq
ℤq+-grp = fld.+-grp

-- -}
-- -}
-- -}
-- -}

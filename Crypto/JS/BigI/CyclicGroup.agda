{-# OPTIONS --without-K #-}
open import Type.Eq using (_==_; Eq?; ≡⇒==; ==⇒≡)
open import FFI.JS using (JS[_]; return; _++_; _>>_)
open import FFI.JS.Check using (check!)

open import FFI.JS.BigI
open import Data.List.Base using (List; foldr)
open import Data.Two.Base using (𝟚; ✓; 0₂; 1₂)
open import Relation.Binary.PropositionalEquality.Base using (_≡_;refl;ap)
open import Relation.Binary.PropositionalEquality.TrustMe
open import Algebra.Raw
open import Algebra.Group
open import Algebra.Group.Homomorphism
import Crypto.JS.BigI.FiniteField as Zq

-- TODO carry on a primality proof of p (also p > 1)
module Crypto.JS.BigI.CyclicGroup (p : BigI) where

-- The constructor mk is not exported.
private
  module Internals where
    data ℤ[_]★ : Set where
      mk : BigI → ℤ[_]★

    mk-inj : ∀ {x y : BigI} → ℤ[_]★.mk x ≡ mk y → x ≡ y
    mk-inj refl = refl

open Internals public using (ℤ[_]★)
open Internals

ℤp★ : Set
ℤp★ = ℤ[_]★

-- There are two ways to go from BigI to ℤp★: BigI▹ℤp★
-- and reducing modulo p which should only be used internally.
-- BigI▹ℤp★ should then be used for any input data as it is untrusted.
BigI▹ℤ[_]★ : BigI → JS[ ℤp★ ]
BigI▹ℤ[_]★ x =
  -- Console.log "BigI▹ℤ[_]★" >>
  check! "below modulus" (x <I p)
         (λ _ → "Not below the modulus: p:" ++
                toString p ++
                " is less than x:" ++
                toString x) >>
  check! "strictcly positive" (x >I 0I)
         (λ _ → "Should be strictly positive: " ++
                toString x ++
                " <= 0") >>
  -- We checked 0 < x < p, so we can use mk
  return (mk x)

-- ℤp★ values are normalized, revealing their representation is therefor ok.
ℤ[_]★▹BigI : ℤp★ → BigI
ℤ[_]★▹BigI (mk x) = x

-- 1 < p, so 1 ∈ ℤp★
1# : ℤp★
1# = mk 1I

-- Because the input in of type ℤp★ the BigI is non-zero,
-- which is the precondition for modInv.
-- The result is wrapped with mk since the result of modInv
-- should already be modulo p.
1/_ : ℤp★ → ℤp★
1/ (mk x) = mk (modInv x p)

-- The result is wrapped with mk since the result of modPow
-- should already be modulo p.
_^I_ : ℤp★ → BigI → ℤp★
mk x ^I y = mk (modPow x y p)

BigI▹ℤp★ = BigI▹ℤ[_]★
ℤp★▹BigI = ℤ[_]★▹BigI

instance
  ℤ[_]★-Eq? : Eq? ℤp★
  ℤ[_]★-Eq? = record
    { _==_ = _=='_
    ; ≡⇒== = ≡⇒=='
    ; ==⇒≡ = ==⇒≡' }
    where
      _=='_ : ℤp★ → ℤp★ → 𝟚
      mk x ==' mk y = x == y
      ≡⇒==' : ∀ {x y} → x ≡ y → ✓ (x ==' y)
      ≡⇒==' {mk x} {mk y} p = ≡⇒== (mk-inj p)
      ==⇒≡' : ∀ {x y} → ✓ (x ==' y) → x ≡ y
      ==⇒≡' {mk x} {mk y} p = ap mk (==⇒≡ p)

ℤp★-Eq?  = ℤ[_]★-Eq?

_**_ _//_ : ℤp★ → ℤp★ → ℤp★

x ** y = mk (mod (multiply (ℤp★▹BigI x) (ℤp★▹BigI y)) p)
x // y = x ** 1/ y

prod : List ℤp★ → ℤp★
prod = foldr _**_ 1#

mon-ops : Monoid-Ops ℤp★
mon-ops = _**_ , 1#

grp-ops : Group-Ops ℤp★
grp-ops = mon-ops , 1/_

postulate grp-struct : Group-Struct grp-ops

grp : Group ℤp★
grp = grp-ops , grp-struct

module grp = Group grp

ℤ[_]★-grp : Group ℤp★
ℤ[_]★-grp = grp

ℤp★-grp : Group ℤp★
ℤp★-grp = grp

module ^-hom {q} where
  open Zq hiding (_^I_)

  _^_ : ℤp★ → ℤ[ q ] → ℤp★
  b ^ e = b ^I ℤ[ q ]▹BigI e

  -- TODO check on the assumptions on p,q
  postulate ^-hom  : ∀ b → GroupHomomorphism ℤ[ q ]+-grp ℤp★-grp (_^_ b)
  postulate ^-comm : ∀ {α x y} → (α ^ x)^ y ≡ (α ^ y)^ x

-- -}
-- -}
-- -}
-- -}
-- -}

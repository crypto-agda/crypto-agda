{-# OPTIONS --without-K #-}
open import Type.Eq
open import FFI.JS using (JS[_]; return; Bool; _++_; _>>_)
open import FFI.JS.Check using (check!)

open import FFI.JS.BigI
open import Data.List.Base using (List; foldr)
open import Data.Two hiding (_==_)
open import Relation.Binary.PropositionalEquality
open import Algebra.Raw
open import Algebra.Group

-- TODO carry on a primality proof of p
module Crypto.JS.BigI.CyclicGroup (p : BigI) where

abstract
  ℤ[_]★ : Set
  ℤ[_]★ = BigI

  private
    ℤp★ : Set
    ℤp★ = BigI

    mod-p : BigI → ℤp★
    mod-p x = mod x p

  -- There are two ways to go from BigI to ℤp★: check and mod-p
  -- Use check for untrusted input data and mod-p for internal
  -- computation.
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
    return x

  repr : ℤp★ → BigI
  repr x = x

  1# : ℤp★
  1# = 1I

  1/_ : ℤp★ → ℤp★
  1/ x = modInv x p

  _^_ : ℤp★ → BigI → ℤp★
  x ^ y = modPow x y p

_*_ _/_ : ℤp★ → ℤp★ → ℤp★

x * y = mod-p (multiply (repr x) (repr y))
x / y = x * 1/ y

instance
  ℤ[_]★-Eq? : Eq? ℤp★
  ℤ[_]★-Eq? = record
    { _==_ = _=='_
    ; ≡⇒== = ≡⇒=='
    ; ==⇒≡ = ==⇒≡' }
    where
      _=='_ : ℤp★ → ℤp★ → 𝟚
      x ==' y = equals (repr x) (repr y)
      postulate
        ≡⇒==' : ∀ {x y} → x ≡ y → ✓ (x ==' y)
        ==⇒≡' : ∀ {x y} → ✓ (x ==' y) → x ≡ y

prod : List ℤp★ → ℤp★
prod = foldr _*_ 1#

mon-ops : Monoid-Ops ℤp★
mon-ops = _*_ , 1#

grp-ops : Group-Ops ℤp★
grp-ops = mon-ops , 1/_

postulate
  grp-struct : Group-Struct grp-ops

grp : Group ℤp★
grp = grp-ops , grp-struct

module grp = Group grp
-- -}
-- -}
-- -}
-- -}
-- -}

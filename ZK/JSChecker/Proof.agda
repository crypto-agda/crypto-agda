{-# OPTIONS --without-K #-}
open import ZK.JSChecker using (verify-PoK-CP-EG-rnd; PoK-CP-EG-rnd; module PoK-CP-EG-rnd)
open import FFI.JS.BigI using (BigI)
open import Data.Product using (_,_)
open import Crypto.JS.BigI.FiniteField
open import Crypto.JS.BigI.CyclicGroup
open import Relation.Binary.PropositionalEquality.Base using (_≡_; refl)
import ZK.GroupHom.ElGamal.JS

module ZK.JSChecker.Proof (p q : BigI) (pok : PoK-CP-EG-rnd ℤ[ q ] ℤ[ p ]★) where

open module ^-h = ^-hom p {q} using (_^_)
open module pok = PoK-CP-EG-rnd pok

pf : ZK.GroupHom.ElGamal.JS.known-enc-rnd.verify-transcript p q g y (g ^ m) (α , β) (A , B) (ℤq▹BigI q c) s
   ≡ verify-PoK-CP-EG-rnd p q pok
pf = refl

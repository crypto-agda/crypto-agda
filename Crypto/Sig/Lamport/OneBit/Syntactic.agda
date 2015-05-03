{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Type.Eq using (Eq?; _==_; ≡⇒==; ==⇒≡)
open import Function
open import Relation.Binary.PropositionalEquality.NP
open ≡-Reasoning
import Crypto.Sig.Lamport.OneBit.Abstract
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits

module Crypto.Sig.Lamport.OneBit.Syntactic
          (Secret : Type)
          (eq? : Eq? Secret)
          where

data Digest : Type where
  hash : Secret → Digest

unhash : Digest → Secret
unhash (hash s) = s

hash-inj : Injective hash
hash-inj = ap unhash

eq?-Digest : Eq? Digest
eq?-Digest = record
  { _==_ = _==_ on unhash
  ; ≡⇒== = λ { {hash x} {hash y} e → ≡⇒== (hash-inj e) }
  ; ==⇒≡ = λ { {hash x} {hash y} e → ap hash (==⇒≡ e) } }

open Crypto.Sig.Lamport.OneBit.Abstract Secret Digest hash eq?-Digest public

open Assuming-injectivity hash-inj
open Assuming-invertibility unhash (λ x → idp) (λ { (hash x) → idp })

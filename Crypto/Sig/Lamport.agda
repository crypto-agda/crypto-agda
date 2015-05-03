{-# OPTIONS --without-K #-}
open import Function using (_∘_)
open import Data.Nat.NP hiding (_==_)
open import Data.Product.NP hiding (map)
open import Data.Bit hiding (_==_)
open import Data.Bits
open import Data.Bits.Properties
open import Data.Vec.NP
open import Relation.Binary.PropositionalEquality.NP
import Crypto.Sig.LamportOneBit

module Crypto.Sig.Lamport
          (#digest  : ℕ)
          (#seed    : ℕ)
          (#secret  : ℕ)
          (#message : ℕ)
          (hash-secret    : Bits #secret → Bits #digest)
          (seed-expansion : Bits #seed   → Bits (#message * 2* #secret))
          where

module OTS1 = Crypto.Sig.LamportOneBit #secret #digest hash-secret

H = hash-secret

#signkey1   = OTS1.#signkey
#verifkey1  = OTS1.#verifkey
#signature1 = OTS1.#signature
#signkey    = #message * #signkey1
#verifkey   = #message * #verifkey1
#signature  = #message * #signature1

Digest     = Bits #digest
Seed       = Bits #seed
Secret     = Bits #secret
SignKey    = Bits #signkey
Message    = Bits #message
Signature  = Bits #signature
VerifKey   = Bits #verifkey

verif-key : SignKey → VerifKey
verif-key = map* #message OTS1.verif-key

module verifkey (vk : VerifKey) where
  vk1s = group #message #verifkey1 vk

module signkey (sk : SignKey) where
  sk1s = group #message #signkey1 sk
  vk   = verif-key sk
  open verifkey vk public

module signature (sig : Signature) where
  sig1s = group #message #signature1 sig

key-gen : Seed → VerifKey × SignKey
key-gen s = vk , sk
  module key-gen where
    sk = seed-expansion s
    vk = verif-key sk

sign : SignKey → Message → Signature
sign sk m = sig
  module sign where
    open signkey sk public
    sig1s = map OTS1.sign sk1s ⊛ m
    sig   = concat sig1s

verify : VerifKey → Message → Signature → Bit
verify vk m sig = and (map OTS1.verify vk1s ⊛ m ⊛ sig1s)
  module verify where
    open verifkey  vk  public
    open signature sig public

verify-correct-sig : ∀ sk m → verify (verif-key sk) m (sign sk m) ≡ 1b
verify-correct-sig = lemma
  where
    module lemma {#m} sk b m where
      skL  = take #signkey1 sk
      skH  = drop #signkey1 sk
      vkL  = OTS1.verif-key skL
      vkH  = map* #m OTS1.verif-key skH
      sigL = OTS1.sign skL b
      sigH = concat (map OTS1.sign (group #m #signkey1 skH) ⊛ m)

    lemma : ∀ {#m} sk m → and (map OTS1.verify (group #m #verifkey1 (map* #m OTS1.verif-key sk)) ⊛ m ⊛ group #m #signature1
                               (concat (map OTS1.sign (group #m #signkey1 sk) ⊛ m))) ≡ 1b
    lemma sk [] = refl
    lemma sk (b ∷ m)
      rewrite (let open lemma sk b m in take-++ #verifkey1 vkL vkH)
            | (let open lemma sk b m in drop-++ #verifkey1 vkL vkH)
            | (let open lemma sk b m in take-++ #signature1 sigL sigH)
            | (let open lemma sk b m in drop-++ #signature1 sigL sigH)
            | (let open lemma sk b m in OTS1.verify-correct-sig skL b)
            | (let open lemma sk b m in lemma skH m)
            = refl
-- -}
-- -}
-- -}
-- -}

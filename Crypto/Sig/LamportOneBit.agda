{-# OPTIONS --without-K #-}
open import Data.Nat.NP hiding (_==_)
open import Data.Product.NP hiding (map)
open import Data.Bit hiding (_==_)
open import Data.Bits
open import Data.Bits.Properties
open import Data.Vec.NP
open import Relation.Binary.PropositionalEquality.NP

module Crypto.Sig.LamportOneBit
          (#secret : ℕ)
          (#digest : ℕ)
          (hash    : Bits #secret → Bits #digest)
          where

#signkey   = 2* #secret
#verifkey  = 2* #digest
#signature = #secret

Digest     = Bits #digest
Secret     = Bits #secret
SignKey    = Bits #signkey
Signature  = Bits #signature
VerifKey   = Bits #verifkey

module signkey (sk : SignKey) where
  skL = take #secret sk
  skH = drop #secret sk
  vkL = hash skL
  vkH = hash skH
  skP = skL , skH

-- Derive the public key by hashing each secret
verif-key : SignKey → VerifKey
verif-key = map2* #secret #digest hash

module verifkey (vk : VerifKey) where
  vkL = take #digest vk
  vkH = drop #digest vk

-- Key generation
key-gen : SignKey → VerifKey × SignKey
key-gen sk = vk , sk
  module key-gen where
    vk = verif-key sk

-- Sign a single bit message
sign : SignKey → Bit → Signature
sign sk b = take2* _ b sk

-- Verify the signature of a single bit message
verify : VerifKey → Bit → Signature → Bit
verify vk b sig = take2* _ b vk == hash sig

verifkey-is-hash-sig : ∀ sk b → take2* _ b (verif-key sk) ≡ hash (sign sk b)
verifkey-is-hash-sig sk 0b = take-++ #digest (hash (take #secret sk)) _
verifkey-is-hash-sig sk 1b = drop-++ #digest (hash (take #secret sk)) _

verify-correct-sig : ∀ sk b → verify (verif-key sk) b (sign sk b) ≡ 1b
verify-correct-sig sk b = ==-reflexive (verifkey-is-hash-sig sk b)

sign-both-reveals-signkey : ∀ sk → sign sk 0b ++ sign sk 1b ≡ sk
sign-both-reveals-signkey = take-drop-lem #secret

import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits

module Assuming-injectivity (hash-inj : Injective hash) where

  -- If one considers the hash function injective, then, so is verif-key
  verif-key-inj : ∀ {sk1 sk2} → verif-key sk1 ≡ verif-key sk2 → sk1 ≡ sk2
  verif-key-inj {sk1} {sk2} e
    = take-drop= #secret sk1 sk2
        (hash-inj (++-inj₁ e))
        (hash-inj (++-inj₂ sk1.vkL sk2.vkL e))
    where
      module sk1 = signkey sk1
      module sk2 = signkey sk2

  -- Therefor under this assumption, different secret keys means different public keys
  verif-key-corrolary : ∀ {sk1 sk2} → sk1 ≢ sk2 → verif-key sk1 ≢ verif-key sk2
  verif-key-corrolary {sk1} {sk2} sk≢ vk= = sk≢ (verif-key-inj vk=)

  -- If one considers the hash function injective then there is
  -- only one signing key which can sign correctly all (0 and 1)
  -- the messages
  signkey-uniqness :
        ∀ sk1 sk2 →
          (∀ b → verify (verif-key sk1) b (sign sk2 b) ≡ 1b) →
          sk1 ≡ sk2
  signkey-uniqness sk1 sk2 e
    = take-drop= #secret sk1 sk2 (lemmaL (e 0b)) (lemmaH (e 1b))
    where
      module sk1 = signkey sk1
      module sk2 = signkey sk2
      lemmaL : verify (verif-key sk1) 0b (sign sk2 0b) ≡ 1b →
              sk1.skL ≡ sk2.skL
      lemmaL e0
        rewrite take-++ #digest sk1.vkL sk1.vkH
              | hash-inj (==⇒≡ e0)
              = refl

      lemmaH : verify (verif-key sk1) 1b (sign sk2 1b) ≡ 1b →
               sk1.skH ≡ sk2.skH
      lemmaH e1
        rewrite drop-++ #digest sk1.vkL sk1.vkH
              | hash-inj (==⇒≡ e1)
              = refl

module Assuming-invertibility
         (unhash : Digest → Secret)
         (unhash-hash : ∀ x → unhash (hash x) ≡ x)
         (hash-unhash : ∀ x → hash (unhash x) ≡ x)
         where

  -- EXERCISES
  {-
  recover-signkey : VerifKey → SignKey
  recover-signkey = {!!}

  recover-signkey-correct : ∀ sk → recover-signkey (verif-key sk) ≡ sk
  recover-signkey-correct = {!!}

  forgesig : VerifKey → Bit → Signature
  forgesig = {!!}

  forgesig-correct : ∀ vk b → verify vk b (forgesig vk b) ≡ 1b
  forgesig-correct = {!!}
  -}

-- -}

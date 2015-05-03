{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Type.Eq using (Eq?; _==_; ≡⇒==; ==⇒≡)
open import Data.Product.NP using (_×_; _,_; fst; snd; map)
open import Data.Bit using (Bit; 0b; 1b; proj′; ✓→≡; ≡→✓)
open import Relation.Binary.PropositionalEquality.NP
open ≡-Reasoning

module Crypto.Sig.Lamport.OneBit.Abstract
          (Secret : Type)
          (Digest : Type)
          (hash   : Secret → Digest)
          (eq?    : Eq? Digest)
          where

SignKey    = Secret × Secret
Signature  = Secret
VerifKey   = Digest × Digest

module signkey (sk : SignKey) where
  skL = fst sk
  skH = snd sk
  vkL = hash skL
  vkH = hash skH

-- Derive the public key by hashing each secret
verif-key : SignKey → VerifKey
verif-key sk = vkL , vkH
  where open signkey sk

module verifkey (vk : VerifKey) where
  vkL = fst vk
  vkH = snd vk

-- Key generation
key-gen : SignKey → VerifKey × SignKey
key-gen sk = vk , sk
  module key-gen where
    vk = verif-key sk

-- Sign a single bit message
sign : SignKey → Bit → Signature
sign = proj′

-- Verify the signature of a single bit message
verify : VerifKey → Bit → Signature → Bit
verify vk b sig = proj′ vk b == hash sig

verify-correct-sig : ∀ sk b → verify (verif-key sk) b (sign sk b) ≡ 1b
verify-correct-sig sk 0b = ✓→≡ (≡⇒== (hash (fst sk) ∎))
verify-correct-sig sk 1b = ✓→≡ (≡⇒== (hash (snd sk) ∎))

import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits

module Assuming-injectivity (hash-inj : Injective hash) where

  -- If one considers the hash function injective, then, so is verif-key
  verif-key-inj : ∀ {sk1 sk2} → verif-key sk1 ≡ verif-key sk2 → sk1 ≡ sk2
  verif-key-inj {sk1} {sk2} e
    = ap₂ _,_ (hash-inj (ap fst e)) (hash-inj (ap snd e))
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
    = ap₂ _,_ (hash-inj (==⇒≡ (≡→✓ (e 0b))))
              (hash-inj (==⇒≡ (≡→✓ (e 1b))))

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

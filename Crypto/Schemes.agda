{-# OPTIONS --without-K #-}
module Crypto.Schemes where

open import Type
open import Data.Product
open import Data.Two.Base
open import Data.Maybe.Base
open import Relation.Binary.PropositionalEquality.Base

record Pubkey-encryption-types : Type₁ where
  field
    PubKey SecKey Message CipherText Rₖ Rₑ : Type

record Pubkey-encryption-ops (pkt : Pubkey-encryption-types) : Type where
  open Pubkey-encryption-types pkt
  field
    key-gen : Rₖ → PubKey × SecKey
    enc : PubKey → Message → Rₑ → CipherText
    dec : SecKey → CipherText → Maybe Message

record Pubkey-encryption : Type₁ where
  field
    pkt : Pubkey-encryption-types
    pko : Pubkey-encryption-ops pkt

  open Pubkey-encryption-types pkt public
  open Pubkey-encryption-ops   pko public

  Functionally-correct =
    ∀ rₖ rₑ m → let (pk , sk) = key-gen rₖ in
               dec sk (enc pk m rₑ) ≡ just m

  field
    functionally-correct : Functionally-correct

record Pubkey-reencryption (pke : Pubkey-encryption) : Type where
  open Pubkey-encryption pke

  field
    reenc : PubKey → CipherText → Rₑ → CipherText

  Correct-reencryption =
     ∀ rₖ m r₀ r₁ → let (pk , sk) = key-gen rₖ in
                    dec sk (reenc pk (enc pk m r₁) r₀) ≡ just m

  field
    correct-reencryption : Correct-reencryption

record Pubkey-homomorphic (pke : Pubkey-encryption) : Type where
  open Pubkey-encryption pke

  field
    _*M_  : Message → Message → Message
    _*CT_ : CipherText → CipherText → CipherText

  Homomorphic =
     ∀ rₖ m₀ m₁ r₀ r₁ → let (pk , sk) = key-gen rₖ in
                        dec sk ((enc pk m₀ r₀) *CT (enc pk m₁ r₁)) ≡ just (m₀ *M m₁)

  field
    homomorphic : Homomorphic

record PoK-message-equality-enc (pke : Pubkey-encryption) : Type₁ where
  open Pubkey-encryption pke
  field
    Proof  : Type
    prove  : Message → PubKey ² → Rₑ ² → CipherText ² → Proof
    verify : CipherText ² → Proof → 𝟚

    correct-pok : ∀ m pk rₑ →
                  let ct = λ b → enc (pk b) m (rₑ b) in
                  verify ct (prove m pk rₑ ct) ≡ 1₂

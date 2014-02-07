{-# OPTIONS --without-K #-}
open import Type
open import Data.Product
open import Relation.Binary.PropositionalEquality.NP

module Cipher.ElGamal.Generic
  (Message : ★)
  (ℤq      : ★)
  (G       : ★)
  (g       : G)
  (_^_     : G → ℤq → G)

  -- Required for encryption
  (_♦_     : G → Message → Message)

  -- Required for decryption
  (_/_     : Message → G → Message)
  where

PubKey     = G
SecKey     = ℤq
CipherText = G × Message
Rₖ         = ℤq
Rₑ         = ℤq

PubKeyGen : Rₖ → PubKey
PubKeyGen x = g ^ x

KeyGen : Rₖ → PubKey × SecKey
KeyGen x = (g ^ x , x)

Enc : PubKey → Message → Rₑ → CipherText
Enc gˣ m y = gʸ , ζ where
  gʸ = g  ^ y
  δ  = gˣ ^ y
  ζ  = δ  ♦ m

Dec : SecKey → CipherText → Message
Dec x (gʸ , ζ) = ζ / (gʸ ^ x)

module FunctionalCorrectness
    (/-♦    : ∀ {x y} → (x ♦ y) / x ≡ y)
    (comm-^ : ∀ {α x y} → (α ^ x)^ y ≡ (α ^ y)^ x)
    where

    functional-correctness : ∀ x y m → Dec x (Enc (g ^ x) m y) ≡ m
    functional-correctness x y m = ap Ctx comm-^ ∙ /-♦
      where Ctx = λ z → (z ♦ m) / ((g ^ y)^ x)

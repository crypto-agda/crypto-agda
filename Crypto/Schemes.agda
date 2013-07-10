{-# OPTIONS --without-K #-}
module Crypto.Schemes where

open import Type
open import Data.Product
open import Relation.Binary.PropositionalEquality

record PublicKeyEncryption : ★₁ where
  constructor mk
  field
    PubKey SecKey Message CipherText Rₖ Rₑ : ★
    KeyGen : Rₖ → PubKey × SecKey
    Enc : PubKey → Message → Rₑ → CipherText
    Dec : SecKey → CipherText → Message

  FunctionallyCorrect : ★
  FunctionallyCorrect =
    ∀ rₖ rₑ m → let (pk , sk) = KeyGen rₖ in
                 Dec sk (Enc pk m rₑ) ≡ m

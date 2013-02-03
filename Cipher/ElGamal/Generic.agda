open import Type
open import Data.Product

module Cipher.ElGamal.Generic
  (Message : ★)
  (ℤq      : ★)
  (G       : ★)
  (g       : G)
  (_^_     : G → ℤq → G)

  -- Required for encryption
  (_∙_     : G → Message → Message)

  -- Required for decryption
  (_/_     : Message → G → Message)
where

PubKey     = G
SecKey     = ℤq
CipherText = G × Message
Rₖ         = ℤq
Rₑ         = ℤq

KeyGen : Rₖ → PubKey × SecKey
KeyGen x = (g ^ x , x)

Enc : PubKey → Message → Rₑ → CipherText
Enc gˣ m y = gʸ , ζ where
  gʸ = g  ^ y
  δ  = gˣ ^ y
  ζ  = δ  ∙ m

Dec : SecKey → CipherText → Message
Dec x (gʸ , ζ) = ζ / (gʸ ^ x)

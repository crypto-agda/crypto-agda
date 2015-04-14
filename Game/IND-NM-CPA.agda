{-# OPTIONS --without-K #-}
open import Type
open import Function
open import Data.Product
open import Data.Two
open import Data.List
open import Data.Maybe

module Game.IND-NM-CPA
  (PubKey     : ★)
  (SecKey     : ★)
  (Message    : ★)
  (CipherText : ★)

  -- randomness supply for: encryption, key-generation, adversary, extensions
  (Rₑ Rₖ Rₐ : ★)

  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : PubKey → Message → Rₑ → CipherText)
  where

challenge : PubKey → 𝟚 → Message ² → Rₑ → CipherText
challenge pk b m rₑ = Enc pk (m b) rₑ

-- IND-CPA adversary in two parts
record Adversary : ★ where
  field
    -- In the step 'm', the adversary receives some randomness,
    -- the public key, the message we want (m₀ or m₁). The adversary
    -- returns the message to encrypt. Remember that the adversary
    -- is a pure and deterministic function, therefore 𝟚 → Message
    -- is the same as Message × Message.
    m  : Rₐ → PubKey → 𝟚 → Message

    -- In the step 'q' the adversary receives the same randomness
    -- supply and public key as in step 'm' and receives the ciphertext
    -- computed by the challenger. The adversary has produce a list
    -- of ciphertext he whishes to decrypt.
    q : Rₐ → PubKey → CipherText → List CipherText

    -- In the step 'b′' the adversary receives the same randomness
    -- supply and public key as in step 'm' and receives the ciphertext
    -- computed by the challenger as in step 'q'. He also receives
    -- a list of messages which are the decryption of ciphertexts
    -- from step 'q'. messages might be '⊥' ('nothing') if the
    -- adversary tried to decrypt the challenge.
    b′ : Rₐ → PubKey → CipherText → List (Maybe Message) → 𝟚

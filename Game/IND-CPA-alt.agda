
{-# OPTIONS --without-K #-}
open import Type
open import Data.Product
open import Data.Bit

module Game.IND-CPA-alt
  (PubKey     : ★)
  (SecKey     : ★)
  (Message    : ★)
  (CipherText : ★)

  -- randomness supply for: encryption, key-generation, adversary, extensions
  (Rₑ Rₖ Rₐ : ★)

  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : PubKey → Message → Rₑ → CipherText)

  where

M² = Bit → Message

-- IND-CPA adversary in two parts
Adv : ★
Adv = Rₐ → PubKey → (M² × (CipherText → Bit))

-- IND-CPA randomness supply
R : ★
R = (Rₐ × Rₖ × Rₑ)

-- IND-CPA games:
--   * input: adversary and randomness supply
--   * output b: adversary claims we are in game ⅁ b
Game : ★
Game = Adv → R → Bit

-- The game step by step:
-- (pk) key-generation, only the public-key is needed
-- (mb) send randomness, public-key and bit
--      receive which message to encrypt
-- (c)  encrypt the message
-- (b′) send randomness, public-key and ciphertext
--      receive the guess from the adversary
⅁ : Bit → Game
⅁ b m (rₐ , rₖ , rₑ) = b′
  where
  pk = proj₁ (KeyGen rₖ)
  ad = m rₐ pk
  mb = proj₁ ad b
  c  = Enc pk mb rₑ
  b′ = proj₂ ad c

⅁₀ ⅁₁ : Game
⅁₀ = ⅁ 0b
⅁₁ = ⅁ 1b

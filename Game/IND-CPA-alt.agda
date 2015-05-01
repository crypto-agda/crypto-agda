{-# OPTIONS --without-K #-}
open import Type
open import Data.Product.NP
open import Data.Two

open import Crypto.Schemes

module Game.IND-CPA-alt
  (pke : Pubkey-encryption)
  (Rₐ : Type)
  where

open Pubkey-encryption pke
M² = Message ²

-- IND-CPA adversary in two parts
Adv : ★
Adv = Rₐ → PubKey → (M² × (CipherText → 𝟚))

-- IND-CPA randomness supply
R : ★
R = (Rₐ × Rₖ × Rₑ)

-- IND-CPA games:
--   * input: adversary and randomness supply
--   * output b: adversary claims we are in game b
Game : ★
Game = Adv → R → 𝟚

-- The game step by step:
-- (pk) key-generation, only the public-key is needed
-- (mb) send randomness, public-key and bit
--      receive which message to encrypt
-- (c)  encrypt the message
-- (b′) send randomness, public-key and ciphertext
--      receive the guess from the adversary
EXP : 𝟚 → Game
EXP b m (rₐ , rₖ , rₑ) = b'
  where
  pk = fst (key-gen rₖ)
  ad = m rₐ pk
  mb = fst ad b
  c  = enc pk mb rₑ
  b' = snd ad c

EXP₀ EXP₁ : Game
EXP₀ = EXP 0₂
EXP₁ = EXP 1₂

game : Adv → (𝟚 × R) → 𝟚
game A (b , r) = b == EXP b A r

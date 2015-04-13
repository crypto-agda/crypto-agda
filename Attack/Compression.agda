{-# OPTIONS --copatterns #-}
-- Compression can be used an an Oracle to defeat encryption.
-- Here we show how compressing before encrypting lead to a
-- NOT semantically secure construction (IND-CPA).
module Attack.Compression where

open import Type using (★)
open import Function.NP
open import Data.Nat.NP
open import Data.Two renaming (_==_ to _==ᵇ_)
open import Data.Product
open import Data.Zero
open import Relation.Binary.PropositionalEquality.NP

import Game.IND-CPA

record Sized (A : ★) : ★ where
  field
    size  : A → ℕ

open Sized {{...}}

module EqSized {A B : ★} {{_ : Sized A}} {{_ : Sized B}} where
    -- Same size
    _==ˢ_ : A → B → 𝟚
    x ==ˢ y = size x == size y

    -- Same size
    _≡ˢ_ : A → B → ★
    x ≡ˢ y = size x ≡ size y

    ≡ˢ→==ˢ : ∀ {x y} → x ≡ˢ y → (x ==ˢ y) ≡ 1₂
    ≡ˢ→==ˢ {x} {y} x≡ˢy rewrite x≡ˢy = ✓→≡ (==.refl {size y})

    ==ˢ→≡ˢ : ∀ {x y} → (x ==ˢ y) ≡ 1₂ → x ≡ˢ y
    ==ˢ→≡ˢ p = ==.sound _ _ (≡→✓ p)

module EncSized
         {PubKey Message CipherText Rₑ : ★}
         (enc  : PubKey → Message → Rₑ → CipherText)
         {{_ : Sized Message}}
         {{_ : Sized CipherText}}
  where
    open EqSized

    -- Encryption size is independant of the randomness
    EncSizeRndInd =
      ∀ {pk m r₀ r₁} → enc pk m r₀ ≡ˢ enc pk m r₁

    -- Encrypted ciphertexts of the same size, will lead to messages of the same size
    EncLeakSize =
      ∀ {pk m₀ m₁ r₀ r₁} → enc pk m₀ r₀ ≡ˢ enc pk m₁ r₁ → m₀ ≡ˢ m₁

module M
  {Message CompressedMessage : ★}
  {{_ : Sized CompressedMessage}}

  (compress : Message → CompressedMessage)

  -- 2 messages which have different size after compression
  (m₀ m₁ : Message)
  (different-compression
     : size (compress m₀) ≢ size (compress m₁))

  (PubKey     : ★)
  (SecKey     : ★)
  (CipherText : ★)
  {{_ : Sized CipherText}}
  (Rₑ Rₖ Rₓ : ★)
  (KeyGen : Rₖ → PubKey × SecKey)
  (enc : PubKey → CompressedMessage → Rₑ → CipherText)
  (open EncSized enc)
  (encSizeRndInd : EncSizeRndInd)
  (encLeakSize : EncLeakSize)
  where

  -- Our adversary runs one encryption
  Rₐ = Rₑ

  CEnc : PubKey → Message → Rₑ → CipherText
  CEnc pk m rₑ = enc pk (compress m) rₑ

  module IND-CPA = Game.IND-CPA PubKey SecKey Message CipherText
                                Rₑ Rₖ Rₐ Rₓ KeyGen CEnc
  open IND-CPA.Adversary
  open EqSized {CipherText}{CipherText} {{it}} {{it}}

  A : IND-CPA.Adversary
  m  A = λ _ _ → [0: m₀ 1: m₁ ]
  b′ A = λ rₑ pk c → c ==ˢ CEnc pk m₁ rₑ

  -- The adversary A is always winning.
  A-always-wins : ∀ b r → IND-CPA.EXP b A r ≡ b
  A-always-wins 0₂ _ = ≢1→≡0 (different-compression ∘′ encLeakSize ∘′ ==ˢ→≡ˢ)
  A-always-wins 1₂ _ = ≡ˢ→==ˢ encSizeRndInd

  -- One should be able to derive this one from A-always-wins and the game-flipping general lemma in the exploration lib
  {-
  A-always-wins' : ∀ r → IND-CPA.game A r ≡ 1₂
  A-always-wins' (0₂ , r) = {!lem (not (IND-CPA.EXP 0₂ {!A!} r)) (IND-CPA.EXP 1₂ A r) (A-always-wins 0₂ r)!}
    where
    lem : ∀ x y → (x ==ᵇ y) ≡ 0₂ → not (x ==ᵇ y) ≡ 1₂
    lem 1₂ 1₂ = λ ()
    lem 1₂ 0₂ = λ _ → refl
    lem 0₂ 1₂ = λ _ → refl
    lem 0₂ 0₂ = λ ()
  A-always-wins' (1₂ , r) = A-always-wins 1₂ r
  -}

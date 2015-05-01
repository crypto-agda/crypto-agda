{-# OPTIONS --copatterns --without-K #-}
-- Compression can be used an an Oracle to defeat encryption.
-- Here we show how compressing before encrypting lead to a
-- NOT semantically secure construction (IND-CPA).
module Attack.Compression where

open import Type using (Type)
open import Function.NP
open import Data.Nat.NP
open import Data.Two renaming (_==_ to _==ᵇ_)
open import Data.Two.Equality
open import Data.Product
open import Data.Zero
open import Relation.Binary.PropositionalEquality.NP

import Game.IND-CPA.Core

record Sized (A : Type) : Type where
  field
    size  : A → ℕ

open Sized {{...}}

module EqSized {A B : Type} {{_ : Sized A}} {{_ : Sized B}} where
    -- Same size
    _==ˢ_ : A → B → 𝟚
    x ==ˢ y = size x == size y

    -- Same size
    _≡ˢ_ : A → B → Type
    x ≡ˢ y = size x ≡ size y

    ≡ˢ→==ˢ : ∀ {x y} → x ≡ˢ y → (x ==ˢ y) ≡ 1₂
    ≡ˢ→==ˢ {x} {y} x≡ˢy rewrite x≡ˢy = ✓→≡ (==.refl {size y})

    ==ˢ→≡ˢ : ∀ {x y} → (x ==ˢ y) ≡ 1₂ → x ≡ˢ y
    ==ˢ→≡ˢ p = ==.sound _ _ (≡→✓ p)

module EncSized
         {PubKey Message CipherText Rₑ : Type}
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
  {Message CompressedMessage : Type}
  {{_ : Sized CompressedMessage}}

  (compress : Message → CompressedMessage)

  -- 2 messages which have different size after compression
  (m₀ m₁ : Message)
  (different-compression
     : size (compress m₀) ≢ size (compress m₁))

  (PubKey     : Type)
  (SecKey     : Type)
  (CipherText : Type)
  {{_ : Sized CipherText}}
  (Rₑ Rₖ Rₓ : Type)
  (KeyGen : Rₖ → PubKey × SecKey)
  (enc : PubKey → CompressedMessage → Rₑ → CipherText)
  (open EncSized enc)
  (encSizeRndInd : EncSizeRndInd)
  (encLeakSize : EncLeakSize)
  where

  -- Our adversary runs one encryption
  Rₐ = Rₑ

  cenc : PubKey → Message → Rₑ → CipherText
  cenc pk m rₑ = enc pk (compress m) rₑ

  module IND-CPA = Game.IND-CPA.Core PubKey SecKey Message CipherText
                                Rₑ Rₖ Rₐ Rₓ KeyGen cenc
  open IND-CPA.Adversary
  open EqSized {CipherText}{CipherText} {{it}} {{it}}

  A : IND-CPA.Adversary
  m A _ _ = [0: m₀ 1: m₁ ]
  b′ A rₑ pk c = c ==ˢ cenc pk m₁ rₑ

  A-always-guesses-right : ∀ b r → IND-CPA.EXP b A r ≡ b
  A-always-guesses-right 0₂ _ = ≢1→≡0 (different-compression ∘′ encLeakSize ∘′ ==ˢ→≡ˢ)
  A-always-guesses-right 1₂ _ = ≡ˢ→==ˢ encSizeRndInd

  -- The adversary A is always winning.
  A-always-wins : ∀ r → IND-CPA.game A r ≡ 1₂
  A-always-wins (b , r) rewrite A-always-guesses-right b r = ==-≡1₂.refl {b}

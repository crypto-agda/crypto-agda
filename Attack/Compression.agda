{-# OPTIONS --copatterns #-}
-- Compression can be used an an Oracle to defeat encryption.
-- Here we show how compressing before encrypting lead to a
-- NOT semantically secure construction (IND-CPA).
module Attack.Compression where

open import Type using (★)
open import Function
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

module _ {A B} {{_ : Sized A}} {{_ : Sized B}} where
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

module _ {PubKey Message CipherText Rₑ : ★}
         (Enc  : PubKey → Message → Rₑ → CipherText)
         {{_ : Sized Message}}
         {{_ : Sized CipherText}}
  where
    -- Encryption size is independant of the randomness
    EncSizeRndInd =
      ∀ {pk m r₀ r₁} → Enc pk m r₀ ≡ˢ Enc pk m r₁

    -- Encrypted ciphertexts of the same size, will lead to messages of the same size
    EncLeakSize =
      ∀ {pk m₀ m₁ r₀ r₁} → Enc pk m₀ r₀ ≡ˢ Enc pk m₁ r₁ → m₀ ≡ˢ m₁

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
  (Enc₀ : PubKey → CompressedMessage → Rₑ → CipherText)
  (Enc₀SizeRndInd : EncSizeRndInd Enc₀)
  (Enc₀LeakSize : EncLeakSize Enc₀)
  where

  -- Our adversary runs one encryption
  Rₐ = Rₑ

  Enc₁ : PubKey → Message → Rₑ → CipherText
  Enc₁ pk m rₑ = Enc₀ pk (compress m) rₑ

  module IND-CPA = Game.IND-CPA PubKey SecKey Message CipherText
                                Rₑ Rₖ Rₐ Rₓ KeyGen Enc₁
  open IND-CPA.Adversary

  A : IND-CPA.Adversary
  m  A = λ _ _ → [0: m₀ 1: m₁ ]
  b′ A = λ rₑ pk c → c ==ˢ Enc₁ pk m₁ rₑ

  -- The adversary A is always winning.
  A-always-wins : ∀ b r → IND-CPA.EXP b A r ≡ b
  A-always-wins 0₂ _ = ≢1→≡0 (different-compression ∘ Enc₀LeakSize ∘ ==ˢ→≡ˢ)
  A-always-wins 1₂ _ = ≡ˢ→==ˢ Enc₀SizeRndInd

  lem : ∀ x y → (x ==ᵇ y) ≡ 0₂ → not (x ==ᵇ y) ≡ 1₂
  lem 1₂ 1₂ = λ ()
  lem 1₂ 0₂ = λ _ → refl
  lem 0₂ 1₂ = λ _ → refl
  lem 0₂ 0₂ = λ ()

  {-
  A-always-wins' : ∀ r → IND-CPA.game A r ≡ 1₂
  A-always-wins' (0₂ , r) = {!lem (not (IND-CPA.EXP 0₂ {!A!} r)) (IND-CPA.EXP 1₂ A r) (A-always-wins 0₂ r)!}
  A-always-wins' (1₂ , r) = A-always-wins 1₂ r
  -}

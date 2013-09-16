-- Compression can be used an an Oracle to defeat encryption.
-- Here we show how compressing before encrypting lead to a
-- NOT semantically secure construction (IND-CPA).
module Attack.Compression where

open import Type using (★)
open import Function
open import Data.Nat.NP
open import Data.Two hiding (_==_)
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
  (m : 𝟚 → Message)
  (different-compression
     : size (compress (m 0₂)) ≢ size (compress (m 1₂)))

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

  adv : IND-CPA.Adv
  adv = (λ { _  _    → m })
      , (λ { rₑ pk c → c ==ˢ Enc₁ pk (m 1₂) rₑ })

  -- The adversary adv is always winning.
  adv-win : ∀ {r} b → IND-CPA.⅁ b adv r ≡ b
  adv-win 0₂ = ≢1→≡0 (different-compression ∘ Enc₀LeakSize ∘ ==ˢ→≡ˢ)
  adv-win 1₂ = ≡ˢ→==ˢ Enc₀SizeRndInd

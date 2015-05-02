{-# OPTIONS --without-K #-}
{-# OPTIONS --copatterns #-}
open import Type
open import Function
open import Function.Extensionality
open import Data.Product.NP
open import Data.Nat.NP hiding (_^_; _==_)
open import Data.Nat.Distance
open import Data.Zero
open import Data.Two
open import Relation.Binary.NP
open import Data.Bits hiding (_==_)
open import Relation.Binary.PropositionalEquality.NP as ≡ hiding (_∙_)
open import HoTT
open Equivalences
open import Algebra.Group
open import Algebra.Group.Homomorphism
open import Algebra.Group.Isomorphism

open import Explore.Core
open import Explore.Explorable
open import Explore.Universe.Type {𝟘}
open import Explore.Universe.Base
open import Explore.Sum
open import Explore.Product
import Explore.Group as EG

import Game.DDH
import Game.IND-CPA.Core
import Crypto.Cipher.ElGamal.Generic

module Crypto.Cipher.ElGamal.CPA-DDH where

module Core
  (ℤqᵁ     : U)
  (G       : Type)
  (g       : G)
  (_^_     : G → El ℤqᵁ → G)
  (Message : Type)
  (_∙_     : G → Message → Message)
  (_/_     : Message → G → Message)
  (Rₐᵁ      : U)
  where

  ℤq = El ℤqᵁ
  Rₐ  = El Rₐᵁ

  -- gˣ is the pk
  -- x is the sk

  Rₓ : Type
  Rₓ = ℤq

  open Crypto.Cipher.ElGamal.Generic Message Message ℤq G g _^_ _∙_ _/_

  open module IND-CPA = Game.IND-CPA.Core PubKey SecKey Message CipherText Rₑ Rₖ Rₐ Rₓ key-gen enc
         renaming (R to R')

  R'ᵁ = Rₐᵁ ×ᵁ ℤqᵁ ×ᵁ ℤqᵁ ×ᵁ ℤqᵁ
  sumR' = sum R'ᵁ
  R = 𝟚 × R'
  Rᵁ = 𝟚ᵁ ×ᵁ R'ᵁ
  sumR = sum Rᵁ

  sumExtRₐ = sum-ext Rₐᵁ
  sumExtℤq = sum-ext ℤqᵁ
  sumHomR' = sum-hom R'ᵁ
  sumExtR' = sum-ext R'ᵁ

  module DDH = Game.DDH ℤq G g _^_ (𝟚 × Rₐ)

  DDH₀ DDH₁ : DDH.Adv → R → 𝟚
  DDH₀ A (b , rₐ , gˣ , gʸ , gᶻ) = DDH.⅁₀ A ((b , rₐ) , gˣ , gʸ , gᶻ)
  DDH₁ A (b , rₐ , gˣ , gʸ , gᶻ) = DDH.⅁₁ A ((b , rₐ) , gˣ , gʸ , gᶻ)
  
  transformAdv : IND-CPA.Adversary → DDH.Adv
  transformAdv (m , d) (b , rₐ) gˣ gʸ gᶻ = b == b′
               where mb  = m rₐ gˣ b
                     c   = (gʸ , gᶻ ∙ mb)
                     b′  = d rₐ gˣ c

  #q_ : Count ℤq
  #q_ = count ℤqᵁ

  _≈q_ : (f g : ℤq → ℕ) → Type
  f ≈q g = sum ℤqᵁ f ≡ sum ℤqᵁ g

  OTP-LEM = ∀ (O : Message → ℕ) m₀ m₁ →
             (λ x → O((g ^ x) ∙ m₀)) ≈q (λ x → O((g ^ x) ∙ m₁))

  1/2 : R → 𝟚
  1/2 (b , _) = b

  module _ {S} where
    _≈ᴿ_ : (f g : R → S) → Type
    f ≈ᴿ g = ∀ (X : S → ℕ) → sumR (X ∘ f) ≡ sumR (X ∘ g)

  Dist : (f g : R → 𝟚) → ℕ
  Dist f g = dist (count Rᵁ f) (count Rᵁ g)

  dist-cong : ∀  {f g h i} → f ≈ᴿ g → h ≈ᴿ i → Dist f h ≡ Dist g i
  dist-cong {f}{g}{h}{i} f≈g h≈i = ap₂ dist (f≈g 𝟚▹ℕ) (h≈i 𝟚▹ℕ)

  OTP-game : IND-CPA.Adversary → R → 𝟚
  OTP-game (m , d) (b , rₐ , x , y , z) = b == d rₐ gˣ (gʸ , gᶻ ∙ m rₐ gˣ b)
    where gˣ = g ^ x
          gʸ = g ^ y
          gᶻ = g ^ z

  module Proof (otp-lem : OTP-LEM)

               (A : IND-CPA.Adversary) where

    module A = IND-CPA.Adversary A
    A′ = transformAdv A

    thm : 1/2 ≈ᴿ OTP-game A
    thm X =
      sumR' (λ _ → X 0₂) + sumR' (λ _ → X 1₂) ≡⟨ sym (sumHomR' _  _) ⟩
      sumR' (λ _ → X 0₂ + X 1₂)                ≡⟨ sumExtR' (lemma ∘ B 0₂) ⟩
      sumR' (Y 0₂ 0₂ +° Y 1₂ 0₂)                ≡⟨ sumHomR' _ _ ⟩
      sumR' (Y 0₂ 0₂) + sumR' (Y 1₂ 0₂)         ≡⟨ ap (_+_ (sumR' (Y 0₂ 0₂))) lemma2 ⟩
      sumR' (Y 0₂ 0₂) + sumR' (Y 1₂ 1₂)         ∎
      where
        open ≡-Reasoning

        B : 𝟚 → R' → 𝟚
        B b (rₐ , x , y , z) = A.b′ rₐ (g ^ x) (g ^ y , (g ^ z) ∙ A.m rₐ (g ^ x) b)

        Y = λ b b' r → X (b == B b' r)

        lemma : ∀ b → X 0₂ + X 1₂ ≡  X (0₂ == b) + X (1₂ == b)
        lemma 1₂ = refl
        lemma 0₂ = ℕ°.+-comm (X 0₂) _

        lemma2 : sumR' (Y 1₂ 0₂) ≡ sumR' (Y 1₂ 1₂)
        lemma2 = sumExtRₐ λ rₐ →
                 sumExtℤq λ x →
                 sumExtℤq λ y →
                   otp-lem (λ m → X (A.b′ rₐ (g ^ x) (g ^ y , m))) (A.m rₐ (g ^ x) 0₂) (A.m rₐ (g ^ x) 1₂)


    module absDist {DIST : Type}(Dist : (f g : R → 𝟚) → DIST)
      (dist-cong : ∀ {f h i} → h ≈ᴿ i → Dist f h ≡ Dist f i) where
      goal : Dist (IND-CPA.game A) 1/2 ≡ Dist (DDH₀ A′) (DDH₁ A′)
      goal = Dist (IND-CPA.game A) 1/2
           ≡⟨by-definition⟩
             Dist (DDH₀ A′) 1/2
           ≡⟨ dist-cong thm ⟩
             Dist (DDH₀ A′) (OTP-game A)
           ≡⟨by-definition⟩
             Dist (DDH₀ A′) (DDH₁ A′)
           ∎
        where open ≡-Reasoning

    open absDist Dist (λ {f}{h}{i} → dist-cong {f}{f}{h}{i} (λ _ → refl)) public

module ElGamal-IND-CPA-reduces-to-DDH
    (ℤqᵁ : U)
    (ℤq-grp : Group (El ℤqᵁ))
    (G : Type)
    (𝔾 : Group G)
    (g : G)
    (_^_ : G → El ℤqᵁ → G)
    (g^-iso : GroupIsomorphism ℤq-grp 𝔾 (_^_ g))
    (Rₐᵁ : U)
    (Rₐ : El Rₐᵁ)
    {{_ : FunExt}}
    {{_ : UA}}
    where

    open Group 𝔾 using (_∙_; _⁻¹; _/_)

    open Core ℤqᵁ G g _^_ G (flip _∙_) _/_ Rₐᵁ public

    otp-lem : ∀ (O : G → ℕ) m₀ m₁ →
        (λ x → O(m₀ ∙ (g ^ x))) ≈q (λ x → O(m₁ ∙ (g ^ x)))
    otp-lem O m₀ m₁ =
      EG.FromAdequate-sum.k₀*≈k₁* ℤq-grp 𝔾 (_^_ g) g^-iso (adequate-sum ℤqᵁ) O

    thm : ∀ A →
          let A′ = transformAdv A in
          Dist (IND-CPA.game A) 1/2 ≡ Dist (DDH₀ A′) (DDH₁ A′)
    thm = Proof.goal otp-lem

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

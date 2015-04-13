{-# OPTIONS --without-K #-}
{-# OPTIONS --copatterns #-}
open import Type
open import Function
open import Function.Extensionality
open import Data.Product.NP
open import Data.Unit
import Data.Fin.NP as Fin
open Fin using (Fin; zero; suc; Fin▹ℕ) renaming (#_ to ##_)
open import Data.Nat.NP hiding (_^_; _==_)
open import Data.Nat.Distance
open import Data.Bit
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
import Game.IND-CPA
import Cipher.ElGamal.Generic

module elgamal where

module El-Gamal-Generic
  (ℤqᵁ : U)
  (G        : ★)
  (g        : G)
  (_^_      : G → El ℤqᵁ → G)
  (Message  : ★)
  (_∙_      : G → Message → Message)
  (_/_      : Message → G → Message)
  (Rₐᵁ       : U)
  where
    ℤq = El ℤqᵁ
    Rₐ  = El Rₐᵁ

    g^_ : ℤq → G
    g^ x = g ^ x

    -- gˣ is the pk
    -- x is the sk

    Rₓ : ★
    Rₓ = ℤq

    open Cipher.ElGamal.Generic Message Message ℤq G g _^_ _∙_ _/_

    module IND-CPA = Game.IND-CPA PubKey SecKey Message CipherText Rₑ Rₖ Rₐ Rₓ KeyGen Enc
    open IND-CPA renaming (R to R')

    -- R' = (Rₐ × Rₖ × Rₑ × Rₓ)
    R'ᵁ = Rₐᵁ ×ᵁ ℤqᵁ ×ᵁ ℤqᵁ ×ᵁ ℤqᵁ
    -- R' = El R'ᵁ
    sumR' = sum R'ᵁ
    R = 𝟚 × R'
    Rᵁ = 𝟚ᵁ ×ᵁ R'ᵁ
    sumR = sum Rᵁ
    
    sumExtRₐ = sum-ext Rₐᵁ
    sumExtℤq = sum-ext ℤqᵁ
    sumHomR' = sum-hom R'ᵁ
    sumExtR' = sum-ext R'ᵁ
    
    IND-CPA-⅁ : IND-CPA.Adversary → R → 𝟚
    IND-CPA-⅁ = IND-CPA.game
    
    module DDH = Game.DDH ℤq G g _^_ (𝟚 × Rₐ)

    DDH-⅁₀ DDH-⅁₁ : DDH.Adv → R → 𝟚
    DDH-⅁₀ A (b , rₐ , gˣ , gʸ , gᶻ) = DDH.⅁₀ A ((b , rₐ) , gˣ , gʸ , gᶻ)
    DDH-⅁₁ A (b , rₐ , gˣ , gʸ , gᶻ) = DDH.⅁₁ A ((b , rₐ) , gˣ , gʸ , gᶻ)
  
    transformAdv : IND-CPA.Adversary → DDH.Adv
    transformAdv (m , d) (b , rₐ) gˣ gʸ gᶻ = b == b′
                 where mb  = m rₐ gˣ b
                       c   = (gʸ , gᶻ ∙ mb)
                       b′  = d rₐ gˣ c

    #q_ : Count ℤq
    #q_ = count ℤqᵁ

    _≈q_ : (f g : ℤq → ℕ) → ★
    f ≈q g = sum ℤqᵁ f ≡ sum ℤqᵁ g

    OTP-LEM = ∀ (O : Message → ℕ) m₀ m₁ →
               (λ x → O((g ^ x) ∙ m₀)) ≈q (λ x → O((g ^ x) ∙ m₁))

    1/2 : R → 𝟚
    1/2 (b , _) = b

    module _ {S} where 
      _≈ᴿ_ : (f g : R → S) → ★
      f ≈ᴿ g = ∀ (X : S → ℕ) → sumR (X ∘ f) ≡ sumR (X ∘ g) 

    Dist : (f g : R → 𝟚) → ℕ
    Dist f g = dist (count Rᵁ f) (count Rᵁ g)

    dist-cong : ∀  {f g h i} → f ≈ᴿ g → h ≈ᴿ i → Dist f h ≡ Dist g i
    dist-cong {f}{g}{h}{i} f≈g h≈i = ap₂ dist (f≈g 𝟚▹ℕ) (h≈i 𝟚▹ℕ)

    OTP-⅁ : IND-CPA.Adversary → R → 𝟚
    OTP-⅁ (m , d) (b , rₐ , x , y , z) = b == d rₐ gˣ (gʸ , gᶻ ∙ m rₐ gˣ b)
      where gˣ = g ^ x
            gʸ = g ^ y
            gᶻ = g ^ z

    module Proof (otp-lem : OTP-LEM)

                 (A : IND-CPA.Adversary) where

        module A = IND-CPA.Adversary A
        A′ = transformAdv A

        goal4 : 1/2 ≈ᴿ OTP-⅁ A
        goal4 X = sumR' (λ _ → X 0b) + sumR' (λ _ → X 1b)
                ≡⟨ sym (sumHomR' _  _) ⟩
                  sumR' (λ _ → X 0b + X 1b)
                ≡⟨ sumExtR' (lemma ∘ B 0b) ⟩
                  sumR' (Y 0b 0b +° Y 1b 0b)
                ≡⟨ sumHomR' _ _ ⟩
                  sumR' (Y 0b 0b) + sumR' (Y 1b 0b)
                ≡⟨ cong (_+_ (sumR' (Y 0b 0b))) lemma2 ⟩
                  sumR' (Y 0b 0b) + sumR' (Y 1b 1b)
                ∎
          where
            open ≡-Reasoning

            B : 𝟚 → R' → 𝟚
            B b (rₐ , x , y , z) = A.b′ rₐ (g ^ x) (g ^ y , (g ^ z) ∙ A.m rₐ (g ^ x) b)

            Y = λ bb bbb r → X (bb == B bbb r)

            lemma : ∀ b → X 0b + X 1b ≡  X (0b == b) + X (1b == b)
            lemma 1b = refl
            lemma 0b = ℕ°.+-comm (X 0b) _

            lemma2 : sumR' (Y 1b 0b) ≡ sumR' (Y 1b 1b)
            lemma2 = sumExtRₐ λ rₐ →
                     sumExtℤq λ x →
                     sumExtℤq λ y →
                       otp-lem (λ m → X (A.b′ rₐ (g ^ x) (g ^ y , m))) (A.m rₐ (g ^ x) 0₂) (A.m rₐ (g ^ x) 1₂)


        module absDist {DIST : ★}(Dist : (f g : R → 𝟚) → DIST)
          (dist-cong : ∀ {f h i} → h ≈ᴿ i → Dist f h ≡ Dist f i) where
          goal : Dist (IND-CPA-⅁ A) 1/2 ≡ Dist (DDH-⅁₀ A′) (DDH-⅁₁ A′)
          goal = Dist (IND-CPA-⅁ A) 1/2
               ≡⟨ refl ⟩
                 Dist (DDH-⅁₀ A′) 1/2
               ≡⟨ dist-cong goal4 ⟩
                 Dist (DDH-⅁₀ A′) (OTP-⅁ A)
               ≡⟨ refl ⟩
                 Dist (DDH-⅁₀ A′) (DDH-⅁₁ A′)
               ∎
            where open ≡-Reasoning

        open absDist Dist (λ {f}{h}{i} → dist-cong {f}{f}{h}{i} (λ _ → refl)) public

module El-Gamal-Base
    (ℤqᵁ : U)
    (ℤq-grp : Group (El ℤqᵁ))
    (G : ★)
    (G-grp : Group G)
    (g : G)
    (_^_ : G → El ℤqᵁ → G)
    (g^-iso : GroupIsomorphism ℤq-grp G-grp (_^_ g))
    (Rₐᵁ : U)
    (Rₐ : El Rₐᵁ)
    {{_ : FunExt}}
    {{_ : UA}}
    where

    open Group ℤq-grp using () renaming (_∙_ to _⊞_)
    module g^ = GroupIsomorphism g^-iso

    open Group G-grp using (_∙_; _⁻¹; _/_)

    open El-Gamal-Generic ℤqᵁ G g _^_ G (flip _∙_) _/_ Rₐᵁ public

    otp-lem : ∀ (O : G → ℕ) m₀ m₁ →
        (λ x → O(m₀ ∙ (g ^ x))) ≈q (λ x → O(m₁ ∙ (g ^ x)))
    otp-lem O m₀ m₁ =
      EG.FromAdequate-sum.k₀*≈k₁* ℤq-grp G-grp (_^_ g) g^-iso (adequate-sum ℤqᵁ) O

    open Proof otp-lem

    thm : ∀ A →
          let A′ = transformAdv A in
          Dist (IND-CPA-⅁ A) 1/2 ≡ Dist (DDH-⅁₀ A′) (DDH-⅁₁ A′)
    thm = goal

        -- -}
        -- -}
        -- -}
        -- -}
        -- -}
        -- -}

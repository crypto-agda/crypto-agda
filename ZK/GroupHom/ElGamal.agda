{-# OPTIONS --without-K #-}
{-
Four kind of ZK proofs about ElGamal encryption:
  (1) proof of encryption:       r = enc y M r ≡ ct
  (2) proof of decryption:       sk = (pub-of sk ≡ y) × (dec sk ct ≡ M)
  (3) proof of equal encryption: (M , r₀ , r₁) = enc y₀ M r₀ ≡ ct₀ × enc y₁ M r₁ ≡ ct₁
  (4) proof of equal decryption: sk = pub-of sk ≡ y × dec sk ct₀ ≡ dec sk ct₁
-}
open import Type using (Type)
open import Type.Eq
open import Function.NP using (flip; _∘_; it)
open import Data.Product.NP
open import Data.Two hiding (_²)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.NP using (idp; _≡_; ap; ap₂; !_; _∙_; module ≡-Reasoning)
open import Algebra.Group
open import Algebra.Group.Constructions
open import Algebra.Group.Homomorphism
import ZK.GroupHom
open import ZK.GroupHom.Types

module ZK.GroupHom.ElGamal
  (G+ G* : Type)
  (𝔾+ : Group G+)
  (𝔾* : Group G*)
  (G*-eq? : Eq? G*)
  (_^_ : G* → G+ → G*)
  (^-hom : ∀ b → GroupHomomorphism 𝔾+ 𝔾* (_^_ b))
  (^-comm : ∀ {α x y} → (α ^ x)^ y ≡ (α ^ y)^ x)
  (g : G*)
  where

module 𝔾* = Group 𝔾*
open Additive-Group 𝔾+
open module MG = Multiplicative-Group 𝔾* hiding (_^_; _²)
module ^ b = GroupHomomorphism (^-hom b)

_² : Type → Type
A ² = A × A

open import Crypto.Cipher.ElGamal.Group 𝔾+ 𝔾* g _^_ ^-comm

EncRnd = Rₑ {- randomness used for encryption of ct -}

open Product

_²-grp : {A : Type} → Group A → Group (A ²)
𝔸 ²-grp = ×-grp 𝔸 𝔸

𝕄 : Group Message
𝕄 = 𝔾*

ℂ𝕋 : Group CipherText
ℂ𝕋 = ×-grp 𝔾* 𝔾*

-- CP : (g₀ g₁ u₀ u₁ : G) (w : ℤq) → Type
-- CP g₀ g₁ u₀ u₁ w = (g₀ ^ w ≡ u₀) × (g₁ ^ w ≡ u₁)

-- CP : (g₀ g₁ u₀ u₁ : G*) (w : G+) → Type
-- CP g₀ g₁ u₀ u₁ w = ✓ (((g₀ ^ w) == u₀) ∧ ((g₁ ^ w) == u₁))

module Known-enc-rnd
         (y  : PubKey)
         (M  : Message)
         (ct : CipherText)
         where
  module ct = CipherText ct

  Valid-witness : EncRnd → Type
  Valid-witness r = enc y M r ≡ ct

  zk-hom : ZK-hom _ _ Valid-witness
  zk-hom = record
    { φ-hom = < ^-hom g , ^-hom y >-hom
    ; y = ct.α , ct.β / M
    ; φ⇒P = λ _ e → ap₂ (λ p q → fst p , q) e
                         (ap (flip _*_ M ∘ snd) e ∙ /-*)
    ; P⇒φ = λ _ e → ap₂ _,_ (ap fst e)
                             (! *-/ ∙ ap (flip _/_ M) (ap snd e))
    }

open ≡-Reasoning

x/′y≡1→x≡y : ∀ {x y} → x ⁻¹ * y ≡ 1# → x ≡ y
x/′y≡1→x≡y e = cancels-*-left (fst ⁻¹-inverse ∙ ! e)

module Known-dec
         (y  : PubKey)
         (M  : Message)
         (ct : CipherText)
         where
  module ct = CipherText ct

  Valid-witness : SecKey → Type
  Valid-witness sk = (pub-of sk ≡ y) × (dec sk ct ≡ M)

  zk-hom : ZK-hom _ _ Valid-witness
  zk-hom = record
    { φ-hom = < ^-hom g , ^-hom ct.α >-hom
    ; y = y , ct.β / M
    ; φ⇒P = λ x e → ap fst e , ap (λ z → z ⁻¹ * ct.β) (ap snd e) ∙ /′-/
    ; P⇒φ = λ x e → ap₂ _,_ (fst e) (! /-/′ ∙ ap (_/_ ct.β) (snd e))
    }

-- Inverse of ciphertexts
_⁻¹CT : CipherText → CipherText
(α , β)⁻¹CT = α ⁻¹ , β ⁻¹

-- Division of ciphertexts
_/CT_ : CipherText → CipherText → CipherText
(α₀ , β₀) /CT (α₁ , β₁) = (α₀ / α₁) , (β₀ / β₁)

-- TODO: Move this elsewhere (Cipher.ElGamal.Homomorphic)
import Algebra.FunctionProperties.Eq as FP
open FP.Implicits
open import Algebra.Group.Abelian
module From-*-comm
         (*-comm : Commutative _*_)
         where
  private
    module 𝔾*-comm = Abelian-Group-Struct (𝔾*.grp-struct , *-comm)

    enc′ : PubKey → (Message × Rₑ) → CipherText
    enc′ y = uncurry (enc y)

  hom-enc : (y : PubKey) → GroupHomomorphism (×-grp 𝕄 𝔾+) ℂ𝕋 (enc′ y)
  hom-enc y = mk λ { {M₀ , r₀} {M₁ , r₁} →
    ap₂ _,_ (^.hom _)
        (enc.β y (M₀ * M₁) (r₀ + r₁)   ≡⟨by-definition⟩
         y ^ (r₀ + r₁)     * (M₀ * M₁) ≡⟨ *= (^.hom y) idp ⟩
         (y ^ r₀ * y ^ r₁) * (M₀ * M₁) ≡⟨ 𝔾*-comm.interchange ⟩
         enc.β y M₀ r₀ * enc.β y M₁ r₁ ∎) }

  module hom-enc y = GroupHomomorphism (hom-enc y)

  -- The encryption of the inverse is the inverse of the encryption
  -- (notice that the randomnesses seems to be negated only because we give an additive notation to our G+ group)
  enc-⁻¹ : ∀ {y M r} → enc y (M ⁻¹) (0− r) ≡ enc y M r ⁻¹CT
  enc-⁻¹ = hom-enc.pres-inv _

  -- The encryption of the division is the division of the encryptions
  -- (notice that the randomnesses seems to be subtracted only because we give an additive notation to our G+ group)
  enc-/ : ∀ {y M₀ r₀ M₁ r₁} → enc y (M₀ / M₁) (r₀ − r₁) ≡ enc y M₀ r₀ /CT enc y M₁ r₁
  enc-/ = hom-enc.−-/ _

  -- Alice wants to prove to the public that she encrypted the
  -- same message for two (potentially different) recepients
  -- without revealing the content of the message or the randomness
  -- used for the encryptions.
  module Message-equality-enc
           (y₀  y₁  : PubKey)
           (ct₀ ct₁ : CipherText)
           where
    module ct₀ = CipherText ct₀
    module ct₁ = CipherText ct₁

    Witness = Message × EncRnd ²
    Statement = CipherText ²

    Valid-witness : Witness → Type
    Valid-witness (M , r₀ , r₁) = enc y₀ M r₀ ≡ ct₀ × enc y₁ M r₁ ≡ ct₁

    private
        θ : Message × EncRnd ² → (Message × EncRnd)²
        θ (M , r₀ , r₁) = ((M , r₀) , (M , r₁))

        θ-hom : GroupHomomorphism (×-grp 𝕄 (𝔾+ ²-grp)) ((×-grp 𝕄 𝔾+)²-grp) θ
        θ-hom = mk idp

    φ-hom : GroupHomomorphism _ _ _
    φ-hom = < hom-enc y₀ × hom-enc y₁ >-hom ∘-hom θ-hom

    zk-hom : ZK-hom _ _ Valid-witness
    zk-hom = record
      { φ-hom = φ-hom
      ; y = ct₀ , ct₁
      ; φ⇒P = λ _ e → ap fst e , ap snd e
      ; P⇒φ = λ x e → ap₂ _,_ (fst e) (snd e)
      }

  module From-flip-^-hom
           (flip-^-hom : ∀ x → GroupHomomorphism 𝔾* 𝔾* (flip _^_ x))
         where
    module flip-^ x = GroupHomomorphism (flip-^-hom x)

    hom-dec : (x : SecKey) → GroupHomomorphism ℂ𝕋 𝕄 (dec x)
    hom-dec x = mk λ { {α₀ , β₀} {α₁ , β₁} →
      dec x (α₀ * α₁ , β₀ * β₁)           ≡⟨by-definition⟩
      ((α₀ * α₁) ^ x)⁻¹ * (β₀ * β₁)       ≡⟨ ap (λ z → _*_ (_⁻¹ z) (_*_ β₀ β₁)) (flip-^.hom x) ⟩
      (α₀ ^ x * α₁ ^ x)⁻¹ * (β₀ * β₁)     ≡⟨ *= 𝔾*-comm.⁻¹-hom idp ⟩
      (α₀ ^ x)⁻¹ * (α₁ ^ x)⁻¹ * (β₀ * β₁) ≡⟨ 𝔾*-comm.interchange ⟩
      dec x (α₀ , β₀) * dec x (α₁ , β₁)   ∎ }

    module hom-dec x = GroupHomomorphism (hom-dec x)

    -- The decryption of the inverse is the inverse of the decryption
    dec-⁻¹ : ∀ {x ct} → dec x (ct ⁻¹CT) ≡ dec x ct ⁻¹
    dec-⁻¹ = hom-dec.pres-inv _

    -- The decryption of the division is the division of the decryptions
    dec-/ : ∀ {x ct₀ ct₁} → dec x (ct₀ /CT ct₁) ≡ dec x ct₀ / dec x ct₁
    dec-/ = hom-dec.−-/ _

    -- Bob wants to prove to the public that he decrypted two
    -- ciphertexts which decrypt to the same message,
    -- without revealing the content of the message or his
    -- secret key.
    -- The two ciphertexts are encrypted using the same public key.
    module Message-equality-dec
         (y : PubKey)
         (ct₀ ct₁ : CipherText)
         where
      private
        module ct₀ = CipherText ct₀
        module ct₁ = CipherText ct₁

        α/ = ct₀.α / ct₁.α
        β/ = ct₀.β / ct₁.β

      Valid-witness : SecKey → Type
      Valid-witness sk = pub-of sk ≡ y × dec sk ct₀ ≡ dec sk ct₁

      zk-hom : ZK-hom _ _ Valid-witness
      zk-hom = record
        { φ-hom = < ^-hom g , ^-hom α/ >-hom
        ; y = y , β/
        ; φ⇒P = λ x e →
                  ap fst e ,
                  x/y≡1→x≡y
                  (dec x ct₀ / dec x ct₁ ≡⟨ ! dec-/ ⟩
                   dec x (ct₀ /CT ct₁) ≡⟨by-definition⟩
                   dec x (α/ , β/) ≡⟨ ! ap (λ z → dec x (α/ , snd z)) e ⟩
                   dec x (α/ , (α/)^ x) ≡⟨ fst ⁻¹-inverse ⟩
                   1# ∎)
        ; P⇒φ = λ x e → ap₂ _,_ (fst e)
                  (x/′y≡1→x≡y
                     (dec x (α/ , β/)       ≡⟨ dec-/ ⟩
                      dec x ct₀ / dec x ct₁ ≡⟨ /= (snd e) idp ⟩
                      dec x ct₁ / dec x ct₁ ≡⟨ snd ⁻¹-inverse ⟩
                      1#                    ∎))
        }

-- -}
-- -}
-- -}

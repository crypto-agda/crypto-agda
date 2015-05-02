open import Algebra.FunctionProperties
open import Function
open import Type using (Type)
open import Data.Product renaming (proj₂ to snd)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality.NP
open import HoTT
open import Algebra.Group
open import Algebra.Group.Homomorphism
open import Algebra.Group.Abelian
open import Algebra.Field
import Crypto.Cipher.ElGamal.Generic
open import Crypto.Schemes

module Crypto.Cipher.ElGamal.Homomorphic where

module Minimal
  (F : Type)
  (G : Type)
  (g : G)
  (_+_ : F → F → F)
  (_^_ : G → F → G)
  (_*_ : G → G → G)
  (_/_ : G → G → G)
  where

  open Crypto.Cipher.ElGamal.Generic G G F G g _^_ _*_ _/_ public

  combine : CipherText → CipherText → CipherText
  combine (a , b) (c , d) = (a * c , b * d)

  reenc : PubKey → CipherText → Rₑ → CipherText
  reenc pk (α , β) rₑ = (g ^ rₑ) * α , (pk ^ rₑ) * β

  module Homomorphic-correctness
      (/-*    : ∀ {x y} → (x * y) / x ≡ y)
      (^-comm : ∀ {α x y} → (α ^ x)^ y ≡ (α ^ y)^ x)
      (*-interchange : ∀ {a b c d} → (a * b) * (c * d) ≡ ((a * c) * (b * d)))
      (^-+-* : ∀ {α x y} → α ^ (x + y) ≡ (α ^ x) * (α ^ y))
      where

    open Functional-correctness /-* ^-comm

    homomorphic-correctness : ∀ sk m₀ m₁ r₀ r₁ →
      let pk = pub-of sk in
      dec sk (combine (enc pk m₀ r₀) (enc pk m₁ r₁)) ≡ m₀ * m₁
    homomorphic-correctness rₖ m₀ m₁ r₀ r₁ =
      (ap (flip _/_ D) p ∙ ap (_/_ N ∘ flip _^_ rₖ) (! ^-+-*)) ∙ functionally-correct rₖ (r₀ + r₁) (m₀ * m₁)
      where D = ((g ^ r₀) * (g ^ r₁))^ rₖ
            N = ((g ^ rₖ) ^ (r₀ + r₁)) * (m₀ * m₁)
            p = *-interchange ∙ ap (flip _*_ (m₀ * m₁)) (! ^-+-*)

    ElGamal-homomorphic : Pubkey-homomorphic ElGamal-encryption
    ElGamal-homomorphic = record { _*M_ = _*_ ; _*CT_ = combine
                                 ; homomorphic = λ sk m₀ m₁ r₀ r₁ → ap just (homomorphic-correctness sk m₀ m₁ r₀ r₁) }

    module Reenc-correctness
        (1# : G)
        (1*-identity : ∀ {x} → 1# * x ≡ x)
        (*1-identity : ∀ {x} → x * 1# ≡ x)
        where

      reenc-combine-1 : ∀ pk c r → reenc pk c r ≡ combine (enc pk 1# r) c
      reenc-combine-1 pk c r = pair= refl (ap (flip _*_ (snd c)) (! *1-identity))

      reenc-correct : ∀ sk m r₀ r₁ →
                      let pk = pub-of sk in
                      dec sk (reenc pk (enc pk m r₁) r₀) ≡ m
      reenc-correct rₖ m r₀ r₁ = ap (λ z → (z * (((g ^ rₖ) ^ r₁) * m)) / D)
                                    (! *1-identity)
                               ∙ homomorphic-correctness rₖ 1# m r₀ r₁
                               ∙ 1*-identity
        where D = ((g ^ r₀) * (g ^ r₁))^ rₖ

      ElGamal-reencryption : Pubkey-reencryption ElGamal-encryption
      ElGamal-reencryption = record { reenc = reenc
                                    ; correct-reencryption = λ sk m r₀ r₁ → ap just (reenc-correct sk m r₀ r₁) }

module Algebraic
  {F  : Type}
  (𝔽+ : Group F) -- No need for the full field, just the additive group
  {G : Type}
  (𝔾 : Abelian-Group G)
  (g : G)
  (_^_ : G → F → G)
  (^-comm : ∀ {α x y} → (α ^ x)^ y ≡ (α ^ y)^ x)
  (^-hom : ∀ {α} → GroupHomomorphism 𝔽+ (Abelian-Group.grp 𝔾) (_^_ α))
  where
  open Additive-Group 𝔽+
  open Multiplicative-Abelian-Group 𝔾 hiding (_^_)
  open Minimal F G g _+_ _^_ _*_ _/′_ public
  open Homomorphic-correctness /′-* ^-comm *-interchange (GroupHomomorphism.hom ^-hom) public
  open Reenc-correctness 1# 1*-identity *1-identity public
-- -}
-- -}
-- -}
-- -}

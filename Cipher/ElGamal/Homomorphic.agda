open import Algebra.FunctionProperties
open import Function
open import Type using (★)
open import Data.Product
open import Relation.Binary.PropositionalEquality.NP
open import HoTT

module Cipher.ElGamal.Homomorphic
  (ℤq  : ★)
  (G   : ★)
  (g   : G)
  (_⊞_ : ℤq → ℤq → ℤq)
  (_^_ : G → ℤq → G)
  (_♦_ : G → G → G)
  (_/_ : G → G → G)
  where

open import Cipher.ElGamal.Generic G ℤq G g _^_ _♦_ _/_

Combine : CipherText → CipherText → CipherText
Combine (a , b) (c , d) = (a ♦ c , b ♦ d)

Reenc : PubKey → CipherText → (rₑ : ℤq) → CipherText
Reenc pk (gʸ , ζ) rₑ = (g ^ rₑ) ♦ gʸ , (pk ^ rₑ) ♦ ζ

module HomomorphicCorrectness
    (/-♦    : ∀ {x y} → (x ♦ y) / x ≡ y)
    (comm-^ : ∀ {α x y} → (α ^ x)^ y ≡ (α ^ y)^ x)
    (interchange-♦ : ∀ {a b c d} → (a ♦ b) ♦ (c ♦ d) ≡ ((a ♦ c) ♦ (b ♦ d)))
    (^-⊞ : ∀ {α x y} → (α ^ x) ♦ (α ^ y) ≡ α ^ (x ⊞ y))
    where

  open FunctionalCorrectness /-♦ comm-^

  homomorphic-correctness : ∀ sk m₀ m₁ r₀ r₁ →
    let pk = PubKeyGen sk in
    Dec sk (Combine (Enc pk m₀ r₀) (Enc pk m₁ r₁)) ≡ m₀ ♦ m₁
  homomorphic-correctness rₖ m₀ m₁ r₀ r₁ =
    (ap (flip _/_ D) p ∙ ap (_/_ N ∘ flip _^_ rₖ) ^-⊞) ∙ functional-correctness rₖ (r₀ ⊞ r₁) (m₀ ♦ m₁)
    where D = ((g ^ r₀) ♦ (g ^ r₁))^ rₖ
          N = ((g ^ rₖ) ^ (r₀ ⊞ r₁)) ♦ (m₀ ♦ m₁)
          p = interchange-♦ ∙ ap (flip _♦_ (m₀ ♦ m₁)) ^-⊞

module ReencCorrectness
    (/-♦    : ∀ {x y} → (x ♦ y) / x ≡ y)
    (comm-^ : ∀ {α x y} → (α ^ x)^ y ≡ (α ^ y)^ x)
    (interchange-♦ : ∀ {a b c d} → (a ♦ b) ♦ (c ♦ d) ≡ ((a ♦ c) ♦ (b ♦ d)))
    (^-⊞ : ∀ {α x y} → (α ^ x) ♦ (α ^ y) ≡ α ^ (x ⊞ y))
    (g⁰ : G)
    (g⁰-idl : ∀ x → g⁰ ♦ x ≡ x)
    (g⁰-idr : ∀ x → x ♦ g⁰ ≡ x)
    where
  open HomomorphicCorrectness /-♦ comm-^ interchange-♦ ^-⊞

  Reenc-Combine-g⁰ : ∀ pk c r → Reenc pk c r ≡ Combine (Enc pk g⁰ r) c
  Reenc-Combine-g⁰ pk c r = pair= refl (ap (flip _♦_ (proj₂ c)) (! (g⁰-idr _)))

  Reenc-correct : ∀ sk m r₀ r₁ →
                  let pk = PubKeyGen sk in
                  Dec sk (Reenc pk (Enc pk m r₁) r₀) ≡ m
  Reenc-correct rₖ m r₀ r₁ = ap (λ z → (z ♦ (((g ^ rₖ) ^ r₁) ♦ m)) / D)
                                (! (g⁰-idr _))
                           ∙ homomorphic-correctness rₖ g⁰ m r₀ r₁
                           ∙ g⁰-idl _
    where D = ((g ^ r₀) ♦ (g ^ r₁))^ rₖ

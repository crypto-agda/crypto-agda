{-# OPTIONS --without-K #-}
{- This file illustrate that if we were given a (non-indexed)
   monad to write randomized programs then we could embed
   randomized programs modeled as deterministic programs taking
   their randomness as an extra argument. -}

open import Type
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (_↔_; module Inverse; sym)
open import Function.Related.TypeIsomorphisms.NP
open import Data.Product
open import Data.Bits
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Nat.Positive
open import Data.Unit
open import Data.Maybe.NP
open import Relation.Binary.PropositionalEquality as ≡ using (→-to-⟶)

module Rand
  (M       : ★ → ★)
  (]0,1[   : ★)
  (_/num+_ : ℕ⁺ → ℕ⁺ → ]0,1[)
  (unit    : ∀ {A} → A → M A)
  (_>>=_   : ∀ {A B} → M A → (A → M B) → M B)
  (map     : ∀ {A B} → (A → B) → M A → M B)
  (choose  : ∀ {A} → ]0,1[ → M A → M A → M A)
 where

Cardinality = ℕ⁺

Rand : ★ → ★
Rand A = Cardinality × M A

embed : ∀ {R A B : ★} → Rand R → (R → A → B) → A → M B
embed (_ , randᴿ) f x = randᴿ >>= λ r → unit (f r x)

1/2 : ]0,1[
1/2 = [ 1 ] /num+ [ 1 ]

rand⊤ : Rand ⊤
rand⊤ = [ 1 ] , unit _

randBit : Rand Bit
randBit = [ 2 ] , choose 1/2 (unit false) (unit true)

_×Rand_ : ∀ {A B} → Rand A → Rand B → Rand (A × B)
(cᴬ , mᴬ) ×Rand (cᴮ , mᴮ) = cᴬˣᴮ , mᴬˣᴮ
  where
  cᴬˣᴮ = cᴬ * cᴮ
  mᴬˣᴮ = mᴬ >>= λ x → mᴮ >>= λ y → unit (x , y)

_⊎Rand_ : ∀ {A B} → Rand A → Rand B → Rand (A ⊎ B)
(cᴬ , mᴬ) ⊎Rand (cᴮ , mᴮ) = cᴬ⁺ᴮ , mᴬ⁺ᴮ
  where
  cᴬ⁺ᴮ    = cᴬ + cᴮ
  cᴬ/cᴬ⁺ᴮ = cᴬ /num+ cᴮ
  mᴬ⁺ᴮ    = choose cᴬ/cᴬ⁺ᴮ (map inj₁ mᴬ) (map inj₂ mᴮ)

mapRand : ∀ {A B} → A ↔ B → Rand A → Rand B
mapRand f (cᴬ , mᴬ) = cᴬ , map f′ mᴬ
  where f′ = _⟨$⟩_ (Inverse.to f)

rand^ : ∀ {A} → Rand A → (n : ℕ) → Rand (A ^ n)
rand^ randᴬ zero    = rand⊤
rand^ randᴬ (suc n) = randᴬ ×Rand (rand^ randᴬ n)

randVec : ∀ {A} → Rand A → (n : ℕ) → Rand (Vec A n)
randVec randᴬ n = mapRand (^↔Vec n) (rand^ randᴬ n)

randBits : ∀ n → Rand (Bits n)
randBits = randVec randBit

randMaybe : ∀ {A} → Rand A → Rand (Maybe A)
randMaybe randᴬ = mapRand (sym Maybe↔⊤⊎) (rand⊤ ⊎Rand randᴬ)

randMaybe^ : ∀ n → Rand (Maybe^ n ⊤)
randMaybe^ zero    = rand⊤
randMaybe^ (suc n) = randMaybe (randMaybe^ n)

randFin1+ : ∀ n → Rand (Fin (suc n))
randFin1+ n = mapRand (Maybe^⊤↔Fin1+ n) (randMaybe^ n)

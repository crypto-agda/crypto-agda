-- Implements ℤq with Data.Fin
open import Type
open import Data.Nat
open import Data.Fin.NP as Fin
open import Relation.Binary.PropositionalEquality

open import Explore.Core
open import Explore.Properties
open import Explore.Explorable
open import Explore.Fin

open Fin.Modulo renaming (sucmod to [suc]; sucmod-inj to [suc]-inj)

module FiniteField.FinImplem (q-1 : ℕ) ([0]' [1]' : Fin (suc q-1))
   {{_ : Postulate-Finˢ-ok}} where
  -- open Sum
  q : ℕ
  q = suc q-1

  ℤq : ★
  ℤq = Fin q

  μℤq : Explorable ℤq
  μℤq = μFin (suc q-1)

  sumℤq : Sum ℤq
  sumℤq = sum μℤq

  [0] : ℤq
  [0] = [0]'

  [1] : ℤq
  [1] = [1]'

  {-
  [suc]-stable : SumStableUnder (sum μℤq) [suc]
  [suc]-stable = {!μFinSUI [suc] [suc]-inj!}
  -}

  _ℕ⊞_ : ℕ → ℤq → ℤq
  zero  ℕ⊞ n = n
  suc m ℕ⊞ n = m ℕ⊞ ([suc] n)

  ℕ⊞-inj : ∀ n {x y} → n ℕ⊞ x ≡ n ℕ⊞ y → x ≡ y
  ℕ⊞-inj zero    eq = eq
  ℕ⊞-inj (suc n) eq = [suc]-inj (ℕ⊞-inj n eq)

  {-
  ℕ⊞-stable : ∀ m → SumStableUnder (sum μℤq) (_ℕ⊞_ m)
  ℕ⊞-stable m = {!μFinSUI (_ℕ⊞_ m) (ℕ⊞-inj m)!}
  -}

  _⊞_ : ℤq → ℤq → ℤq
  m ⊞ n = Fin▹ℕ m ℕ⊞ n

  ⊞-inj : ∀ m {x y} → m ⊞ x ≡ m ⊞ y → x ≡ y
  ⊞-inj m = ℕ⊞-inj (Fin▹ℕ m)

  {-
  ⊞-stable : ∀ m → SumStableUnder (sum μℤq) (_⊞_ m)
  ⊞-stable m = {!μFinSUI (_⊞_ m) (⊞-inj m)!}
  -}

  _ℕ⊠_ : ℕ → ℤq → ℤq
  zero  ℕ⊠ n = [0]
  suc m ℕ⊠ n = n ⊞ (m ℕ⊠ n)

  _⊠_ : ℤq → ℤq → ℤq
  m ⊠ n = Fin▹ℕ m ℕ⊠ n

  _[^]ℕ_ : ℤq → ℕ → ℤq
  m [^]ℕ zero  = [1]
  m [^]ℕ suc n = m ⊠ (m [^]ℕ n)

  _[^]_ : ℤq → ℤq → ℤq
  m [^] n = m [^]ℕ (Fin▹ℕ n)

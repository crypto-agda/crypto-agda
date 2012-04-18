module flipbased-tree where

open import Function
open import Data.Bits
open import Data.Nat.NP
open import Data.Nat.Properties
open import Data.Vec

import flipbased

data Tree {a} (A : Set a) : ℕ → Set a

↺ : ∀ {a} n (A : Set a) → Set a
↺ = flip Tree

-- “↺ n A” reads like: “toss n coins and then return a value of type A”
data Tree {a} (A : Set a) where
  return↺ : ∀ {c} → A → ↺ c A
  fork    : ∀ {c} → (left right : ↺ c A) → ↺ (suc c) A

runDet : ∀ {a} {A : Set a} → ↺ 0 A → A
runDet (return↺ x) = x

toss : ↺ 1 Bit
toss = fork (return↺ 0b) (return↺ 1b)

map↺ : ∀ {c a b} {A : Set a} {B : Set b} → (A → B) → ↺ c A → ↺ c B
map↺ f (return↺ x) = return↺ (f x)
map↺ f (fork left right) = fork (map↺ f left) (map↺ f right)

weaken≤ : ∀ {m c a} {A : Set a} → m ≤ c → ↺ m A → ↺ c A
weaken≤ p (return↺ x) = return↺ x
weaken≤ (s≤s p) (fork left right) = fork (weaken≤ p left) (weaken≤ p right)

weaken+ : ∀ {m c a} {A : Set a} → ↺ m A → ↺ (c + m) A
weaken+ {m} {c} = weaken≤ (ℕ≤.trans (m≤m+n m c) (ℕ≤.reflexive (ℕ°.+-comm m c)))

join↺ : ∀ {c₁ c₂ a} {A : Set a} → ↺ c₁ (↺ c₂ A) → ↺ (c₁ + c₂) A
join↺ {c} (return↺ x)      = weaken+ {_} {c} x
join↺     (fork left right) = fork (join↺ left) (join↺ right)

open flipbased ↺ toss weaken≤ return↺ map↺ join↺ public

open import Data.Bool
open import Data.Bits
open import Data.Product
open import Relation.Binary.PropositionalEquality

infix 4 _/2+_/2
infix 6 _/2
postulate
  [0,1] : Set
  0/1 : [0,1]
  1/1 : [0,1]
  _/2 : [0,1] → [0,1]
  _/2+_/2 : [0,1] → [0,1] → [0,1]
-- sym _/2+_/2
-- 1 /2+ 1 /2 = 1/1
-- p /2+ p /2 = p
-- p /2+ (1- p) /2 = 1/2

1/2^_ : ℕ → [0,1]
1/2^ zero = 1/1
1/2^ suc n = (1/2^ n)/2

1/2 : [0,1]
1/2 = 1/2^ 1
1/4 : [0,1]
1/4 = 1/2^ 2

postulate
  Pr[_≡_] : ∀ {c a} {A : Set a} → ↺ c A → A → [0,1]

_≈_ : ∀ {c a} {A : Set a} (p₁ p₂ : ↺ c A) → Set a
p₁ ≈ p₂ = ∀ x → Pr[ p₁ ≡ x ] ≡ Pr[ p₂ ≡ x ]

postulate
  fork-sym : ∀ {c a} {A : Set a} (p₁ p₂ : ↺ c A) → fork p₁ p₂ ≈ fork p₂ p₁

  Pr-return-≡ : ∀ {c a} {A : Set a} (x : A) → Pr[ return↺ {c = c} x ≡ x ] ≡ 1/1

  Pr-return-≢ : ∀ {c a} {A : Set a} {x y : A} → x ≢ y → Pr[ return↺ {c = c} x ≡ y ] ≡ 0/1

  Pr-fork : ∀ {c a} {A : Set a} {left right : ↺ c A} {x : A} {p q}
            → Pr[ left ≡ x ] ≡ p
            → Pr[ right ≡ x ] ≡ q
            → Pr[ fork left right ≡ x ] ≡ p /2+ q /2

  0/2+p/2≡p/2 : ∀ p → (0/1 /2+ p /2) ≡ p /2

Pr-fork-0 : ∀ {c a} {A : Set a} {left right : ↺ c A} {x : A} {p}
            → Pr[ left ≡ x ] ≡ 0/1
            → Pr[ right ≡ x ] ≡ p
            → Pr[ fork left right ≡ x ] ≡ p /2
Pr-fork-0 {p = p} eq₁ eq₂ rewrite sym (0/2+p/2≡p/2 p) = Pr-fork eq₁ eq₂

ex₁ : ∀ x → Pr[ toss ≡ x ] ≡ 1/2
ex₁ 1b = Pr-fork-0 (Pr-return-≢ (λ ())) (Pr-return-≡ 1b)
ex₁ 0b rewrite fork-sym {0} (return↺ 0b) (return↺ 1b) 0b = Pr-fork-0 (Pr-return-≢ (λ ())) (Pr-return-≡ 0b)

postulate
  ex₂ : ∀ x y → Pr[ toss ⟨,⟩ toss ≡ (x , y) ] ≡ 1/2^ 2

  ex₃ : ∀ {n} (x : Bits n) → Pr[ random ≡ x ] ≡ 1/2^ n

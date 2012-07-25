module flipbased-implem where

open import Function
open import Data.Bits
open import Data.Nat.NP
open import Data.Vec
open import Relation.Binary.NP
open import Relation.Nullary
import Relation.Binary.PropositionalEquality as ≡
import Data.Fin as Fin
open ≡ using (_≗_; _≡_)
open Fin using (Fin; suc)

import flipbased
import flipbased-counting
import flipbased-running

-- “↺ n A” reads like: “toss n coins and then return a value of type A”
record ↺ {a} n (A : Set a) : Set a where
  constructor mk
  field
    run↺ : Bits n → A

open ↺ public

private
  -- If you are not allowed to toss any coin, then you are deterministic.
  Det : ∀ {a} → Set a → Set a
  Det = ↺ 0

runDet : ∀ {a} {A : Set a} → Det A → A
runDet f = run↺ f []

toss : ↺ 1 Bit
toss = mk head

return↺ : ∀ {n a} {A : Set a} → A → ↺ n A
return↺ = mk ∘ const

map↺ : ∀ {n a b} {A : Set a} {B : Set b} → (A → B) → ↺ n A → ↺ n B
map↺ f x = mk (f ∘ run↺ x)
-- map↺ f x ≗ x >>=′ (return {0} ∘ f)

join↺ : ∀ {n₁ n₂ a} {A : Set a} → ↺ n₁ (↺ n₂ A) → ↺ (n₁ + n₂) A
join↺ {n₁} x = mk (λ bs → run↺ (run↺ x (take _ bs)) (drop n₁ bs))
-- join↺ x = x >>= id

comap : ∀ {m n a} {A : Set a} → (Bits n → Bits m) → ↺ m A → ↺ n A
comap f (mk g) = mk (g ∘ f)

private
  take≤ : ∀ {a} {A : Set a} {m n} → n ≤ m → Vec A m → Vec A n
  take≤ z≤n _ = []
  take≤ (s≤s p) (x ∷ xs) = x ∷ take≤ p xs

weaken≤ : ∀ {m n a} {A : Set a} → m ≤ n → ↺ m A → ↺ n A
weaken≤ p = comap (take≤ p)

open flipbased ↺ toss weaken≤ return↺ map↺ join↺ public
open flipbased-running ↺ toss weaken≤ return↺ map↺ join↺ run↺ public
open flipbased-counting ↺ toss weaken≤ return↺ map↺ join↺ count↺ public

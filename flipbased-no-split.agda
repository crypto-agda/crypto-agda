module flipbased-no-split where

open import Function
open import Data.Bits
open import Data.Nat.NP
open import Data.Nat.Properties
open import Data.Vec
open import Data.Product
open import Data.Unit using (⊤)
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
    run↺′ : ∀ {pre post} → Bits (pre + (n + post)) → A

  run↺ : Bits n → A
  run↺ = run↺′ {0} {0} ∘ ≡.subst Bits (ℕ°.+-comm 0 n)

open ↺ public

private
  -- If you are not allowed to toss any coin, then you are deterministic.
  Det : ∀ {a} → Set a → Set a
  Det = ↺ 0

runDet : ∀ {a} {A : Set a} → Det A → A
runDet (mk f) = f {0} {0} []

toss : ↺ 1 Bit
toss = mk (λ {m} → head ∘ drop m)

return↺ : ∀ {n a} {A : Set a} → A → ↺ n A
return↺ x = mk (const x)

map↺ : ∀ {n a b} {A : Set a} {B : Set b} → (A → B) → ↺ n A → ↺ n B
map↺ f (mk g) = mk (λ {m n} → f ∘ g {m} {n})
-- map↺ f x ≗ x >>=′ (return {0} ∘ f)

join↺ : ∀ {n₁ n₂ a} {A : Set a} → ↺ n₁ (↺ n₂ A) → ↺ (n₁ + n₂) A
join↺ {n₁} {n₂} (mk g) = mk (λ {m n} → f m n) where
  f : ∀ m n → Bits (m + ((n₁ + n₂) + n)) → _
  f m n bs = run↺′ (g {m} (bs ₁)) {m + n₁} (bs ₂)
     where _₁ : Bits (m + ((n₁ + n₂) + n)) → Bits (m + (n₁ + (n₂ + n)))
           _₁ rewrite ℕ°.+-assoc n₁ n₂ n = id
           _₂ : Bits (m + ((n₁ + n₂) + n)) → Bits ((m + n₁) + (n₂ + n))
           _₂ rewrite ≡.sym (ℕ°.+-assoc m (n₁ + n₂) n)
                    | ≡.sym (ℕ°.+-assoc m n₁ n₂)
                    | ℕ°.+-assoc (m + n₁) n₂ n = id
-- join↺ x = x >>= id

coe : ∀ {m n} (pf : ∀ m′ n′ → ∃ λ pre → ∃ λ post → m′ + (n + n′) ≡ pre + (m + post))
        {a} {A : Set a} → ↺ m A → ↺ n A
coe {m} {n} pf {A = A} (mk f) = mk (λ {m′ n′} → g m′ n′) where
  g : ∀ m′ n′ → Bits (m′ + (n + n′)) → A
  g m′ n′ bs with pf m′ n′
  ... | pre , post , eq rewrite eq = f {pre} {post} bs

module Redundant where
    weaken′ : ∀ {m n a} {A : Set a} → ↺ m A → ↺ (m + n) A
    weaken′ {m} {n} = coe pf
      where pf : ∀ m′ n′ → ∃ λ pre → ∃ λ post → m′ + ((m + n) + n′) ≡ pre + (m + post)
            pf m′ n′ rewrite ℕ°.+-assoc m n n′ = m′ , n + n′ , ≡.refl

weaken≤ : ∀ {m n a} {A : Set a} → m ≤ n → ↺ m A → ↺ n A
weaken≤ {m} {n} m≤n = coe pf
  where pf : ∀ m′ n′ → ∃ λ pre → ∃ λ post → m′ + (n + n′) ≡ pre + (m + post)
        pf m′ n′  = m′ , n ∸ m + n′ , pf′
           where pf′ : m′ + (n + n′) ≡ m′ + (m + (n ∸ m + n′))
                 pf′ rewrite ≡.sym (ℕ°.+-assoc m (n ∸ m) n′) | m+n∸m≡n m≤n = ≡.refl

open flipbased ↺ toss weaken≤ return↺ map↺ join↺ public
open flipbased-running ↺ toss weaken≤ return↺ map↺ join↺ run↺ public
open flipbased-counting ↺ toss weaken≤ return↺ map↺ join↺ count↺ public

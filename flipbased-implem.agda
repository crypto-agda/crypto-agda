module flipbased-implem where

open import Function
open import Data.Bits
open import Data.Nat.NP
open import Data.Vec
open import Relation.Binary
import Relation.Binary.PropositionalEquality as ≡
import Data.Fin as Fin
open ≡ using (_≗_; _≡_)
open Fin using (Fin; suc)

import flipbased

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

⅁ : ℕ → Set
⅁ n = ↺ n Bit

⅁? : ∀ c → Set
⅁? c = Bit → ⅁ c

count↺ᶠ : ∀ {c} → ⅁ c → Fin (suc (2^ c))
count↺ᶠ f = #⟨ run↺ f ⟩ᶠ

count↺ : ∀ {c} → ⅁ c → ℕ
count↺ f = #⟨ run↺ f ⟩

infix 4 _≗↺_ _≗⅁?_ _≋⅁_

_≗↺_ : ∀ {c a} {A : Set a} (f g : ↺ c A) → Set a
f ≗↺ g = run↺ f ≗ run↺ g

_≗⅁?_ : ∀ {c} (g₀ g₁ : ⅁? c) → Set
g₀ ≗⅁? g₁ = ∀ b → g₀ b ≗↺ g₁ b

-- f ≈⅁ g when f and g return the same number of 1 (and 0).
_≈⅁_ : ∀ {n} (f g : ⅁ n) → Set
_≈⅁_ = _≡_ on count↺

_∼[_]⅁_ : ∀ {m n} → ⅁ m → (ℕ → ℕ → Set) → ⅁ n → Set
_∼[_]⅁_ {m} {n} f _∼_ g = ⟨2^ n * count↺ f ⟩ ∼ ⟨2^ m * count↺ g ⟩

_≋⅁_ : ∀ {m n} → ⅁ m → ⅁ n → Set
f ≋⅁ g = f ∼[ _≡_ ]⅁ g

Safe⅁? : ∀ {c} (f : ⅁? c) → Set
Safe⅁? f = f 0b ≈⅁ f 1b

≈⅁⇒≋⅁ : ∀ {n} {f g : ⅁ n} → f ≈⅁ g → f ≋⅁ g
≈⅁⇒≋⅁ eq rewrite eq = ≡.refl

≗⇒≈⅁ : ∀ {c} {f g : ⅁ c} → f ≗↺ g → f ≈⅁ g
≗⇒≈⅁ {f = f} {g} = ≗-cong-# (run↺ f) (run↺ g)

≗⇒≋⅁ : ∀ {c} {f g : ⅁ c} → f ≗↺ g → f ≋⅁ g
≗⇒≋⅁ eq rewrite ≗⇒≈⅁ eq = ≡.refl

≋⅁⇒≈⅁ : ∀ {n} {f g : ⅁ n} → f ≋⅁ g → f ≈⅁ g
≋⅁⇒≈⅁ {n} = 2^-inj n

module ≗⅁? where
  refl : ∀ {n} {f : ⅁? n} → f ≗⅁? f
  refl _ _ = ≡.refl

  sym : ∀ {n} → Symmetric {A = ⅁? n} _≗⅁?_
  sym p b R = ≡.sym (p b R)

  trans : ∀ {c} → Transitive (_≗⅁?_ {c})
  trans p q b R = ≡.trans (p b R) (q b R)

module ≋⅁ where
  refl : ∀ {n} {f : ⅁ n} → f ≋⅁ f
  refl = ≡.refl

  sym : ∀ {n} → Symmetric {A = ⅁ n} _≋⅁_
  sym = ≡.sym

  trans : ∀ {n} → Transitive {A = ⅁ n} _≋⅁_
  trans = ≡.trans

  cong-≗↺ : ∀ {c c'} {f g : ⅁ c} {f' g' : ⅁ c'} → f ≗↺ g → f' ≗↺ g' → f ≋⅁ f' → g ≋⅁ g'
  cong-≗↺ f≗g f'≗g' f≈f' rewrite ≗⇒≈⅁ f≗g | ≗⇒≈⅁ f'≗g' = f≈f'

module ≈⅁ {n} where
  refl : ∀ {f : ⅁ n} → f ≈⅁ f
  refl = ≡.refl

  sym : Symmetric {A = ⅁ n} _≈⅁_
  sym = ≡.sym

  trans :  Transitive {A = ⅁ n} _≈⅁_
  trans = ≡.trans

  cong-≗↺ : ∀ {f g f' g' : ⅁ n} → f ≗↺ g → f' ≗↺ g' → f ≈⅁ f' → g ≈⅁ g'
  cong-≗↺ f≗g f'≗g' f≈f' rewrite ≗⇒≈⅁ f≗g | ≗⇒≈⅁ f'≗g' = f≈f'

module ⅁? {n} where
  join : ⅁ n → ⅁ n → ⅁? n
  join f g b = if b then f else g

  safe-sym : ∀ {g : ⅁? n} → Safe⅁? g → Safe⅁? (g ∘ not)
  safe-sym {g} g-safe = ≈⅁.sym {n} {g 0b} {g 1b} g-safe

data Rat : Set where _/_ : (num denom : ℕ) → Rat

Pr[_≡1] : ∀ {n} (f : ⅁ n) → Rat
Pr[_≡1] {n} f = count↺ f / 2^ n

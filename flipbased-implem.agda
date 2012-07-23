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

_≗↺_ : ∀ {c a} {A : Set a} (f g : ↺ c A) → Set a
f ≗↺ g = run↺ f ≗ run↺ g

⅁ : ℕ → Set
⅁ n = ↺ n Bit

_≗⅁_ : ∀ {c} (⅁₀ ⅁₁ : Bit → ⅁ c) → Set
⅁₀ ≗⅁ ⅁₁ = ∀ b → ⅁₀ b ≗↺ ⅁₁ b

≗⅁-trans : ∀ {c} → Transitive (_≗⅁_ {c})
≗⅁-trans p q b R = ≡.trans (p b R) (q b R)

count↺ᶠ : ∀ {c} → ⅁ c → Fin (suc (2^ c))
count↺ᶠ f = #⟨ run↺ f ⟩ᶠ

count↺ : ∀ {c} → ⅁ c → ℕ
count↺ = Fin.toℕ ∘ count↺ᶠ

_∼[_]⅁_ : ∀ {m n} → ⅁ m → (ℕ → ℕ → Set) → ⅁ n → Set
_∼[_]⅁_ {m} {n} f _∼_ g = ⟨2^ n * count↺ f ⟩ ∼ ⟨2^ m * count↺ g ⟩

_∼[_]⅁′_ : ∀ {n} → ⅁ n → (ℕ → ℕ → Set) → ⅁ n → Set
_∼[_]⅁′_ {n} f _∼_ g = count↺ f ∼ count↺ g

_≈⅁_ : ∀ {m n} → ⅁ m → ⅁ n → Set
f ≈⅁ g = f ∼[ _≡_ ]⅁ g

_≈⅁′_ : ∀ {n} (f g : ⅁ n) → Set
f ≈⅁′ g = f ∼[ _≡_ ]⅁′ g

≈⅁-refl : ∀ {n} {f : ⅁ n} → f ≈⅁ f
≈⅁-refl = ≡.refl

≈⅁-sym : ∀ {n} → Symmetric {A = ⅁ n} _≈⅁_
≈⅁-sym = ≡.sym

≈⅁-trans : ∀ {n} → Transitive {A = ⅁ n} _≈⅁_
≈⅁-trans = ≡.trans

≗⇒≈⅁ : ∀ {c} {f g : ⅁ c} → f ≗↺ g → f ≈⅁ g
≗⇒≈⅁ pf rewrite ext-# pf = ≡.refl

≈⅁′⇒≈⅁ : ∀ {n} {f g : ⅁ n} → f ≈⅁′ g → f ≈⅁ g
≈⅁′⇒≈⅁ eq rewrite eq = ≡.refl

≈⅁⇒≈⅁′ : ∀ {n} {f g : ⅁ n} → f ≈⅁ g → f ≈⅁′ g
≈⅁⇒≈⅁′ {n} = 2^-inj n

≈⅁-cong : ∀ {c c'} {f g : ⅁ c} {f' g' : ⅁ c'} → f ≗↺ g → f' ≗↺ g' → f ≈⅁ f' → g ≈⅁ g'
≈⅁-cong f≗g f'≗g' f≈f' rewrite ext-# f≗g | ext-# f'≗g' = f≈f'

≈⅁′-cong : ∀ {c} {f g f' g' : ⅁ c} → f ≗↺ g → f' ≗↺ g' → f ≈⅁′ f' → g ≈⅁′ g'
≈⅁′-cong f≗g f'≗g' f≈f' rewrite ext-# f≗g | ext-# f'≗g' = f≈f'

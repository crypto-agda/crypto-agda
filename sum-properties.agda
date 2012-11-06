module sum-properties where

open import Data.Bool.NP
open import Data.Nat.NP

open import Function.NP

open import sum

import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_ ; _≗_)

sum-lem : ∀ {A : Set}(μA : SumProp A)(f g : A → ℕ) → sum μA f ≡ sum μA (λ x → f x ⊓ g x) + sum μA (λ x → f x ∸ g x)
sum-lem μA f g = ≡.trans (sum-ext μA f≗f⊓g+f∸g) (sum-hom μA (λ x → f x ⊓ g x) (λ x → f x ∸ g x))
  where
    f≗f⊓g+f∸g : f ≗ (λ x → f x ⊓ g x + (f x ∸ g x))
    f≗f⊓g+f∸g x = a≡a⊓b+a∸b (f x) (g x)

toℕ-⊓ : ∀ a b → toℕ a ⊓ toℕ b ≡ toℕ (a ∧ b)
toℕ-⊓ true true = ≡.refl
toℕ-⊓ true false = ≡.refl
toℕ-⊓ false b = ≡.refl

toℕ-∸ : ∀ a b → toℕ a ∸ toℕ b ≡ toℕ (a ∧ not b)
toℕ-∸ true true = ≡.refl
toℕ-∸ true false = ≡.refl
toℕ-∸ false true = ≡.refl
toℕ-∸ false false = ≡.refl

count-lem : ∀ {A : Set}(μA : SumProp A)(f g : A → Bool)
          → count μA f ≡ count μA (λ x → f x ∧ g x) + count μA (λ x → f x ∧ not (g x))
count-lem μA f g rewrite sum-lem μA (toℕ ∘ f) (toℕ ∘ g)
                       | sum-ext μA (λ x → toℕ-⊓ (f x) (g x)) 
                       | sum-ext μA (λ x → toℕ-∸ (f x) (g x)) = ≡.refl


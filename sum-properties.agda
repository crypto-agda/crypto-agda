module sum-properties where

open import Type

import Level as L

open import Data.Bool.NP
open import Data.Nat.NP
open import Data.Nat.Properties

open import Function.NP

open import sum

import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_ ; _≗_ ; _≗₂_)

sum-lem : ∀ {A : ★}(μA : SumProp A)(f g : A → ℕ) → sum μA f ≡ sum μA (λ x → f x ⊓ g x) + sum μA (λ x → f x ∸ g x)
sum-lem μA f g = ≡.trans (sum-ext μA f≗f⊓g+f∸g) (sum-hom μA (λ x → f x ⊓ g x) (λ x → f x ∸ g x))
  where
    f≗f⊓g+f∸g : f ≗ (λ x → f x ⊓ g x + (f x ∸ g x))
    f≗f⊓g+f∸g x = a≡a⊓b+a∸b (f x) (g x)

sum-lem₂ : ∀ {A : ★}(μA : SumProp A)(f g : A → ℕ) → sum μA f + sum μA g ≡ sum μA (λ x → f x ⊔ g x) + sum μA (λ x → f x ⊓ g x)
sum-lem₂ μA f g =
         sum μA f + sum μA g ≡⟨ ≡.sym (sum-hom μA f g) ⟩
         sum μA (λ x → f x + g x) ≡⟨ sum-ext μA (λ x → lemma (f x) (g x)) ⟩
         sum μA (λ x → f x ⊔ g x + f x ⊓ g x) ≡⟨ sum-hom μA (λ x → f x ⊔ g x) (λ x → f x ⊓ g x) ⟩
         sum μA (λ x → f x ⊔ g x) + sum μA (λ x → f x ⊓ g x) ∎
  where
    open ≡.≡-Reasoning
    lemma : ∀ a b → a + b ≡ a ⊔ b + a ⊓ b
    lemma zero b rewrite ℕ°.+-comm b 0 = ≡.refl
    lemma (suc a) zero = ≡.refl
    lemma (suc a) (suc b) rewrite +-assoc-comm a 1 b
                                | +-assoc-comm (a ⊔ b) 1 (a ⊓ b) = ≡.cong (suc ∘ suc) (lemma a b)

toℕ-⊓ : ∀ a b → toℕ a ⊓ toℕ b ≡ toℕ (a ∧ b)
toℕ-⊓ true true = ≡.refl
toℕ-⊓ true false = ≡.refl
toℕ-⊓ false b = ≡.refl

toℕ-⊔ : ∀ a b → toℕ a ⊔ toℕ b ≡ toℕ (a ∨ b)
toℕ-⊔ true true = ≡.refl
toℕ-⊔ true false = ≡.refl
toℕ-⊔ false b = ≡.refl

toℕ-∸ : ∀ a b → toℕ a ∸ toℕ b ≡ toℕ (a ∧ not b)
toℕ-∸ true true = ≡.refl
toℕ-∸ true false = ≡.refl
toℕ-∸ false true = ≡.refl
toℕ-∸ false false = ≡.refl

count-lem : ∀ {A : ★}(μA : SumProp A)(f g : A → Bool)
          → count μA f ≡ count μA (λ x → f x ∧ g x) + count μA (λ x → f x ∧ not (g x))
count-lem μA f g rewrite sum-lem μA (toℕ ∘ f) (toℕ ∘ g)
                       | sum-ext μA (λ x → toℕ-⊓ (f x) (g x)) 
                       | sum-ext μA (λ x → toℕ-∸ (f x) (g x)) = ≡.refl

count-lem₂ : ∀ {A : ★}(μA : SumProp A)(f g : A → Bool) → count μA f + count μA g ≡ count μA (λ x → f x ∨ g x) + count μA (λ x → f x ∧ g x)
count-lem₂ μA f g rewrite sum-lem₂ μA (toℕ ∘ f) (toℕ ∘ g)
  | sum-ext μA (λ x → toℕ-⊔ (f x) (g x))
  | sum-ext μA (λ x → toℕ-⊓ (f x) (g x)) = ≡.refl


sum-⊔ : ∀ {A : ★}(μA : SumProp A)(f g : A → ℕ) → sum μA (λ x → f x ⊔ g x) ≤ sum μA f + sum μA g
sum-⊔ μA f g = ℕ≤.trans
                 (sum-mono μA (λ x → ⊔≤+ (f x) (g x)))
                 (ℕ≤.reflexive (sum-hom μA f g))
  where
    ⊔≤+ : ∀ a b → a ⊔ b ≤ a + b
    ⊔≤+ zero b = ℕ≤.refl
    ⊔≤+ (suc a) zero = ℕ≤.reflexive (≡.cong suc (ℕ°.+-comm 0 a))
    ⊔≤+ (suc a) (suc b) = s≤s (ℕ≤.trans (⊔≤+ a b) (ℕ≤.trans (≤-step ℕ≤.refl) (ℕ≤.reflexive (+-assoc-comm 1 a b))))

count-∨ : ∀ {A : ★}(μA : SumProp A)(f g : A → Bool) → count μA (λ x → f x ∨ g x) ≤ count μA f + count μA g
count-∨ μA f g = ℕ≤.trans (ℕ≤.reflexive (sum-ext μA (λ x → ≡.sym (toℕ-⊔ (f x) (g x))))) 
                          (sum-⊔ μA (toℕ ∘ f) (toℕ ∘ g))


sum-ext₂ : ∀ {A B}{f g : A → B → ℕ}(μA : SumProp A)(μB : SumProp B) → f ≗₂ g → sum μA (sum μB ∘ f) ≡ sum μA (sum μB ∘ g)
sum-ext₂ μA μB f≗g = sum-ext μA (sum-ext μB ∘ f≗g)

Injective : ∀ {a b}{A : Set a}{B : Set b}(f : A → B) → Set (a L.⊔ b)
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

StableUnderInjection : ∀ {A} → SumProp A → Set
StableUnderInjection μ = ∀ p → Injective p → SumStableUnder μ p

CountStableUnderInjection : ∀ {A} → SumProp A → Set
CountStableUnderInjection μ = ∀ p → Injective p → CountStableUnder μ p

module _ where
  open import bijection-fin
  open import Data.Fin using (Fin; zero; suc)
  open import Data.Vec.NP renaming (sum to vsum)

  sumFin : ∀ n → Sum (Fin n)
  sumFin n f = vsum (tabulate f)

  sumFin-spec : ∀ n → sumFin (suc n) ≗ sum (μFinSuc n)
  sumFin-spec zero    f = ℕ°.+-comm (f zero) 0
  sumFin-spec (suc n) f = ≡.cong (_+_ (f zero)) (sumFin-spec n (f ∘ suc))

  sumFinSUI : ∀ n f p → Injective p → sumFin n f ≡ sumFin n (f ∘ p)
  sumFinSUI n f p p-inj = count-perm f p (λ x y → p-inj)

  μFinSUI : ∀ {n} → StableUnderInjection (μFinSuc n)
  μFinSUI {n} p p-inj f rewrite ≡.sym (sumFin-spec n f)
                              | ≡.sym (sumFin-spec n (f ∘ p))
                              = sumFinSUI (suc n) f p p-inj

#-StableUnderInjection : ∀ {A}{μ : SumProp A} → StableUnderInjection μ → CountStableUnderInjection μ
#-StableUnderInjection sui p p-inj f = sui p p-inj (toℕ ∘ f)

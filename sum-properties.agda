module sum-properties where

open import Type
import Level as L
open import Data.Bool.NP
open Data.Bool.NP.Indexed
open import Data.Nat.NP
open import Data.Nat.Properties
open import Function.NP
open import sum
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_ ; _≗_ ; _≗₂_)

module _ {A : ★} (μA : SumProp A) (f g : A → ℕ) where
    open ≡.≡-Reasoning

    sum-⊓-∸ : sum μA f ≡ sum μA (f ⊓° g) + sum μA (f ∸° g)
    sum-⊓-∸ = sum μA f                          ≡⟨ sum-ext μA (f ⟨ a≡a⊓b+a∸b ⟩° g) ⟩
              sum μA ((f ⊓° g) +° (f ∸° g))     ≡⟨ sum-hom μA (f ⊓° g) (f ∸° g) ⟩
              sum μA (f ⊓° g) + sum μA (f ∸° g) ∎

    sum-⊔-⊓ : sum μA f + sum μA g ≡ sum μA (f ⊔° g) + sum μA (f ⊓° g)
    sum-⊔-⊓ = sum μA f + sum μA g               ≡⟨ ≡.sym (sum-hom μA f g) ⟩
              sum μA (f +° g)                   ≡⟨ sum-ext μA (f ⟨ a+b≡a⊔b+a⊓b ⟩° g) ⟩
              sum μA (f ⊔° g +° f ⊓° g)         ≡⟨ sum-hom μA (f ⊔° g) (f ⊓° g) ⟩
              sum μA (f ⊔° g) + sum μA (f ⊓° g) ∎

    sum-⊔ : sum μA (f ⊔° g) ≤ sum μA f + sum μA g
    sum-⊔ = ℕ≤.trans (sum-mono μA (f ⟨ ⊔≤+ ⟩° g)) (ℕ≤.reflexive (sum-hom μA f g))

module _M2 {A : ★} (μA : SumProp A) (f g : A → Bool) where
    count-∧-not : count μA f ≡ count μA (f ∧° g) + count μA (f ∧° not° g)
    count-∧-not rewrite sum-⊓-∸ μA (toℕ ∘ f) (toℕ ∘ g)
                      | sum-ext μA (f ⟨ toℕ-⊓ ⟩° g)
                      | sum-ext μA (f ⟨ toℕ-∸ ⟩° g)
                      = ≡.refl

    count-∨-∧ : count μA f + count μA g ≡ count μA (f ∨° g) + count μA (f ∧° g)
    count-∨-∧ rewrite sum-⊔-⊓ μA (toℕ ∘ f) (toℕ ∘ g)
                    | sum-ext μA (f ⟨ toℕ-⊔ ⟩° g)
                    | sum-ext μA (f ⟨ toℕ-⊓ ⟩° g)
                    = ≡.refl

    count-∨≤+ : count μA (f ∨° g) ≤ count μA f + count μA g
    count-∨≤+ = ℕ≤.trans (ℕ≤.reflexive (sum-ext μA (≡.sym ∘ (f ⟨ toℕ-⊔ ⟩° g))))
                         (sum-⊔ μA (toℕ ∘ f) (toℕ ∘ g))

sum-ext₂ : ∀ {A B}{f g : A → B → ℕ}(μA : SumProp A)(μB : SumProp B) → f ≗₂ g → sum μA (sum μB ∘ f) ≡ sum μA (sum μB ∘ g)
sum-ext₂ μA μB f≗g = sum-ext μA (sum-ext μB ∘ f≗g)

Injective : ∀ {a b}{A : Set a}{B : Set b}(f : A → B) → Set (a L.⊔ b)
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

StableUnderInjection : ∀ {A} → SumProp A → Set
StableUnderInjection μ = ∀ p → Injective p → SumStableUnder μ p

CountStableUnderInjection : ∀ {A} → SumProp A → Set
CountStableUnderInjection μ = ∀ p → Injective p → CountStableUnder μ p

module SumFinProperties where
  open import bijection-fin
  open import Data.Fin using (Fin; zero; suc)
  open import Data.Vec.NP renaming (sum to vsum)

  sumFin : ∀ n → Sum (Fin n)
  sumFin n f = vsum (tabulate f)

  sumFin-spec : ∀ n → sumFin (suc n) ≗ sum (μFinSuc n)
  sumFin-spec zero    f = ℕ°.+-comm (f zero) 0
  sumFin-spec (suc n) f = ≡.cong (_+_ (f zero)) (sumFin-spec n (f ∘ suc))

  sumFinSUI : ∀ n f p → Injective p → sumFin n f ≡ sumFin n (f ∘ p)
  sumFinSUI n f p p-inj = count-perm f p (λ _ _ → p-inj)

  μFinSUI : ∀ {n} → StableUnderInjection (μFinSuc n)
  μFinSUI {n} p p-inj f rewrite ≡.sym (sumFin-spec n f)
                              | ≡.sym (sumFin-spec n (f ∘ p))
                              = sumFinSUI (suc n) f p p-inj

#-StableUnderInjection : ∀ {A}{μ : SumProp A} → StableUnderInjection μ → CountStableUnderInjection μ
#-StableUnderInjection sui p p-inj f = sui p p-inj (toℕ ∘ f)

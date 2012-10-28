open import Function
open import Data.Nat
open import Data.Unit
open import Data.Product
open import Data.Bits
open import Data.Bool.NP as Bool
open import Relation.Binary.PropositionalEquality

module sum where

private
    ★₁ : Set₂
    ★₁ = Set₁

    ★ : ★₁
    ★ = Set

Sum : ★ → ★
Sum A = (A → ℕ) → ℕ

Count : ★ → ★
Count A = (A → Bit) → ℕ

SumExt : ∀ {A} → Sum A → ★
SumExt sumA = ∀ {f g} → f ≗ g → sumA f ≡ sumA g

sumToCount : ∀ {A} → Sum A → Count A
sumToCount sumA f = sumA (Bool.toℕ ∘ f)

sum⊤ : Sum ⊤
sum⊤ f = f _

sum⊤-ext : SumExt sum⊤
sum⊤-ext f≗g = f≗g _

sumBit : Sum Bit
sumBit f = f 0b + f 1b

sumBit-ext : SumExt sumBit
sumBit-ext f≗g rewrite f≗g 0b | f≗g 1b = refl

-- liftM2 _,_ in the continuation monad
sumProd : ∀ {A B} → Sum A → Sum B → Sum (A × B)
sumProd sumA sumB f = sumA (λ x₀ →
                        sumB (λ x₁ →
                          f (x₀ , x₁)))

sumProd-ext : ∀ {A B} {sumA : Sum A} {sumB : Sum B} →
              SumExt sumA → SumExt sumB → SumExt (sumProd sumA sumB)
sumProd-ext sumA-ext sumB-ext f≗g = sumA-ext (λ x → sumB-ext (λ y → f≗g (x , y)))

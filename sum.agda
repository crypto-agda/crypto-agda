open import Function
open import Data.Nat.NP
open import Data.Nat.Properties
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
SumExt sumᴬ = ∀ {f g} → f ≗ g → sumᴬ f ≡ sumᴬ g

CountExt : ∀ {A} → Count A → ★
CountExt countᴬ = ∀ {f g} → f ≗ g → countᴬ f ≡ countᴬ g

SumLin : ∀ {A} → Sum A → ★
SumLin sumᴬ = ∀ f k → sumᴬ (λ x → k * f x) ≡ k * sumᴬ f

record SumProp {A} (sumᴬ : Sum A) : ★ where
  constructor mk
  field
    sum-ext : SumExt sumᴬ
    sum-lin : SumLin sumᴬ

  sum : Sum A
  sum = sumᴬ

  Card : ℕ
  Card = sumᴬ (const 1)

  count : Count A
  count f = sumᴬ (Bool.toℕ ∘ f)

  count-ext : CountExt count
  count-ext f≗g = sum-ext (cong Bool.toℕ ∘ f≗g)

open SumProp public

_≈Sum_ : ∀ {A} → (sum₀ sum₁ : Sum A) → ★
sum₀ ≈Sum sum₁ = ∀ f → sum₀ f ≡ sum₁ f

sum⊤ : Sum ⊤
sum⊤ f = f _

μ⊤ : SumProp sum⊤
μ⊤ = mk sum⊤-ext sum⊤-lin
  where
    sum⊤-ext : SumExt sum⊤
    sum⊤-ext f≗g = f≗g _

    sum⊤-lin : SumLin sum⊤
    sum⊤-lin f k = refl

sumBit : Sum Bit
sumBit f = f 0b + f 1b

μBit : SumProp sumBit
μBit = mk sumBit-ext sumBit-lin
  where
    sumBit-ext : SumExt sumBit
    sumBit-ext f≗g rewrite f≗g 0b | f≗g 1b = refl

    sumBit-lin : SumLin sumBit
    sumBit-lin f k
      rewrite ℕ°.*-comm k (f 0b)
            | ℕ°.*-comm k (f 1b)
            | ℕ°.*-comm k (f 0b + f 1b)
            | ℕ°.distribʳ k (f 0b) (f 1b)
            = refl

-- liftM2 _,_ in the continuation monad
_×Sum_ : ∀ {A B} → Sum A → Sum B → Sum (A × B)
(sumᴬ ×Sum sumᴮ) f = sumᴬ (λ x₀ →
                       sumᴮ (λ x₁ →
                         f (x₀ , x₁)))

_×Sum-ext_ : ∀ {A B} {sumᴬ : Sum A} {sumᴮ : Sum B} →
              SumExt sumᴬ → SumExt sumᴮ → SumExt (sumᴬ ×Sum sumᴮ)
(sumA-ext ×Sum-ext sumB-ext) f≗g = sumA-ext (λ x → sumB-ext (λ y → f≗g (x , y)))

_×μ_ : ∀ {A B} {sumᴬ : Sum A} {sumᴮ : Sum B}
              → SumProp sumᴬ
              → SumProp sumᴮ
              → SumProp (sumᴬ ×Sum sumᴮ)
(μA ×μ μB)
   = mk (sum-ext μA ×Sum-ext sum-ext μB) lin
   where
     lin : SumLin (sum μA ×Sum sum μB)
     lin f k rewrite sum-ext μA (λ x → sum-lin μB (λ y → f (x , y)) k) = sum-lin μA (λ x → sum μB (λ y → f (x , y))) k

swapS : ∀ {A B} → Sum (A × B) → Sum (B × A)
swapS sumA×B f = sumA×B (f ∘ swap)

sum-const : ∀ {A} {sumᴬ : Sum A} (μA : SumProp sumᴬ) → ∀ k → sumᴬ (const k) ≡ Card μA * k
sum-const μA k
  rewrite ℕ°.*-comm (Card μA) k
        | sym (sum-lin μA (const 1) k)
        | proj₂ ℕ°.*-identity k = refl

_×Sum-proj₁_ : ∀ {A B} {sumᴬ : Sum A} {sumᴮ : Sum B}
               (μA : SumProp sumᴬ)
               (μB : SumProp sumᴮ)
               f →
               (sumᴬ ×Sum sumᴮ) (f ∘ proj₁) ≡ Card μB * sumᴬ f
_×Sum-proj₁_ {sumᴮ = sumᴮ} (mk sumᴬ-ext sumᴬ-lin) μB f
  rewrite sumᴬ-ext (sum-const μB ∘ f)
        = sumᴬ-lin f (Card μB)

_×Sum-proj₂_ : ∀ {A B} {sumᴬ : Sum A} {sumᴮ : Sum B}
               (μA : SumProp sumᴬ)
               (μB : SumProp sumᴮ)
               f →
               (sumᴬ ×Sum sumᴮ) (f ∘ proj₂) ≡ Card μA * sumᴮ f
(μA ×Sum-proj₂ μB) f = sum-const μA (sum μB f)

_×Sum-proj₁'_ : ∀ {A B} {sumᴬ : Sum A} {sumᴮ : Sum B}
                  (μA : SumProp sumᴬ) (μB : SumProp sumᴮ)
                  {f} {g} →
                  sumᴬ f ≡ sumᴬ g →
                  (sumᴬ ×Sum sumᴮ) (f ∘ proj₁) ≡ (sumᴬ ×Sum sumᴮ) (g ∘ proj₁)
(μA ×Sum-proj₁' μB) {f} {g} sumf≡sumg
  rewrite (μA ×Sum-proj₁ μB) f
        | (μA ×Sum-proj₁ μB) g
        | sumf≡sumg = refl

_×Sum-proj₂'_ : ∀ {A B} {sumᴬ : Sum A} {sumᴮ : Sum B}
                  (μA : SumProp sumᴬ) (μB : SumProp sumᴮ)
                  {f} {g} →
                  sumᴮ f ≡ sumᴮ g →
                  (sumᴬ ×Sum sumᴮ) (f ∘ proj₂) ≡ (sumᴬ ×Sum sumᴮ) (g ∘ proj₂)
(μA ×Sum-proj₂' μB) sumf≡sumg = sum-ext μA (const sumf≡sumg)

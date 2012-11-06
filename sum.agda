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

SumHom : ∀ {A} → Sum A → ★
SumHom sumᴬ = ∀ f g → sumᴬ (λ x → f x + g x) ≡ sumᴬ f + sumᴬ g

record SumProp A : ★ where
  constructor mk
  field
    sum : Sum A
    sum-ext : SumExt sum
    sum-lin : SumLin sum
    sum-hom : SumHom sum

  Card : ℕ
  Card = sum (const 1)

  count : Count A
  count f = sum (Bool.toℕ ∘ f)

  count-ext : CountExt count
  count-ext f≗g = sum-ext (cong Bool.toℕ ∘ f≗g)

open SumProp public

_≈Sum_ : ∀ {A} → (sum₀ sum₁ : Sum A) → ★
sum₀ ≈Sum sum₁ = ∀ f → sum₀ f ≡ sum₁ f

sum⊤ : Sum ⊤
sum⊤ f = f _

μ⊤ : SumProp ⊤
μ⊤ = mk sum⊤ sum⊤-ext sum⊤-lin sum⊤-hom
  where
    sum⊤-ext : SumExt sum⊤
    sum⊤-ext f≗g = f≗g _

    sum⊤-lin : SumLin sum⊤
    sum⊤-lin f k = refl

    sum⊤-hom : SumHom sum⊤
    sum⊤-hom f g = refl

sumBit : Sum Bit
sumBit f = f 0b + f 1b

μBit : SumProp Bit
μBit = mk sumBit sumBit-ext sumBit-lin sumBit-hom
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

    sumBit-hom : SumHom sumBit
    sumBit-hom f g = +-interchange (f 0b) (g 0b) (f 1b) (g 1b)

infixr 4 _×Sum_

-- liftM2 _,_ in the continuation monad
_×Sum_ : ∀ {A B} → Sum A → Sum B → Sum (A × B)
(sumᴬ ×Sum sumᴮ) f = sumᴬ (λ x₀ →
                       sumᴮ (λ x₁ →
                         f (x₀ , x₁)))

_×Sum-ext_ : ∀ {A B} {sumᴬ : Sum A} {sumᴮ : Sum B} →
              SumExt sumᴬ → SumExt sumᴮ → SumExt (sumᴬ ×Sum sumᴮ)
(sumA-ext ×Sum-ext sumB-ext) f≗g = sumA-ext (λ x → sumB-ext (λ y → f≗g (x , y)))

infixr 4 _×μ_

_×μ_ : ∀ {A B} → SumProp A
               → SumProp B
               → SumProp (A × B)
(μA ×μ μB)
   = mk (sum μA ×Sum sum μB) (sum-ext μA ×Sum-ext sum-ext μB) lin hom
   where
     lin : SumLin (sum μA ×Sum sum μB)
     lin f k rewrite sum-ext μA (λ x → sum-lin μB (λ y → f (x , y)) k) = sum-lin μA (sum μB ∘ curry f) k

     hom : SumHom (sum μA ×Sum sum μB)
     hom f g rewrite sum-ext μA (λ x → sum-hom μB (λ y → f (x , y)) (λ y → g (x , y))) 
         = sum-hom μA (sum μB ∘ curry f) (sum μB ∘ curry g)

swapS : ∀ {A B} → Sum (A × B) → Sum (B × A)
swapS sumA×B f = sumA×B (f ∘ swap)

{-
×Sum-swap : ∀ {A B} (sumᴬ : Sum A) (sumᴮ : Sum B) →
              (sumᴬ ×Sum sumᴮ) ≈Sum swapS (sumᴮ ×Sum sumᴬ)
×Sum-swap sumᴬ sumᴮ f = {!!}

-- wrong so far: ×Sum-swap (const 42) (const 1)
-}

-- sum (λ x → f x + g x) ≡ sum f + sum g

sum-const : ∀ {A} (μA : SumProp A) → ∀ k → sum μA (const k) ≡ Card μA * k 
sum-const μA k
  rewrite ℕ°.*-comm (Card μA) k
        | sym (sum-lin μA (const 1) k)
        | proj₂ ℕ°.*-identity k = refl

infixr 4 _×Sum-proj₁_ _×Sum-proj₁'_ _×Sum-proj₂_ _×Sum-proj₂'_

_×Sum-proj₁_ : ∀ {A B}
                 (μA : SumProp A)
                 (μB : SumProp B)
                 f →
                 sum (μA ×μ μB) (f ∘ proj₁) ≡ Card μB * sum μA f
(μA ×Sum-proj₁ μB) f
  rewrite sum-ext μA (sum-const μB ∘ f)
        = sum-lin μA f (Card μB)

_×Sum-proj₂_ : ∀ {A B}
                 (μA : SumProp A)
                 (μB : SumProp B)
                 f →
                 sum (μA ×μ μB) (f ∘ proj₂) ≡ Card μA * sum μB f
(μA ×Sum-proj₂ μB) f = sum-const μA (sum μB f)

_×Sum-proj₁'_ : ∀ {A B}
                  (μA : SumProp A) (μB : SumProp B)
                  {f} {g} →
                  sum μA f ≡ sum μA g →
                  sum (μA ×μ μB) (f ∘ proj₁) ≡ sum (μA ×μ μB) (g ∘ proj₁)
(μA ×Sum-proj₁' μB) {f} {g} sumf≡sumg
  rewrite (μA ×Sum-proj₁ μB) f
        | (μA ×Sum-proj₁ μB) g
        | sumf≡sumg = refl

_×Sum-proj₂'_ : ∀ {A B}
                  (μA : SumProp A) (μB : SumProp B)
                  {f} {g} →
                  sum μB f ≡ sum μB g →
                  sum (μA ×μ μB) (f ∘ proj₂) ≡ sum (μA ×μ μB) (g ∘ proj₂)
(μA ×Sum-proj₂' μB) sumf≡sumg = sum-ext μA (const sumf≡sumg)

open import Data.Fin hiding (_+_)
open import Data.Vec.NP as Vec renaming (map to vmap; sum to vsum)

sumFin : ∀ n → Sum (Fin n)
sumFin n f = vsum (vmap f (allFin n))

μFin : ∀ n → SumProp (Fin n)
μFin n = mk (sumFin n) sumFin-ext sumFin-lin sumFin-hom
  module SumFin where
    sumFin-ext : SumExt (sumFin n)
    sumFin-ext f≗g rewrite map-ext f≗g (allFin n) = refl

    sumFin-lin : SumLin (sumFin n)
    sumFin-lin f x = sum-distribˡ f x (allFin n)
    
    sumFin-hom : SumHom (sumFin n)
    sumFin-hom f g = sum-linear f g (allFin n)

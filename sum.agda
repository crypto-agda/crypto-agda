open import Type
open import Function
open import Data.Nat.NP
open import Data.Nat.Properties
open import Data.Unit hiding (_≤_)
open import Data.Sum
open import Data.Product
open import Data.Bits
open import Data.Bool.NP as Bool
open import Relation.Binary.PropositionalEquality as ≡

module sum where

_≤°_ : ∀ {A : ★}(f g : A → ℕ) → ★
f ≤° g = ∀ x → f x ≤ g x

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

SumMon : ∀ {A} → Sum A → ★
SumMon sumᴬ = ∀ f g → f ≤° g → sumᴬ f ≤ sumᴬ g

record SumLinear {A} sumᴬ : ★ where
  constructor mk
  field
    sum-lin : SumLin {A} sumᴬ
    sum-hom : SumHom sumᴬ

SumSwap : ∀ {A} → Sum A → ★₁
SumSwap {A} sumᴬ = ∀ {B} f {sumᴮ} → SumLinear {B} sumᴮ → sumᴬ (sumᴮ ∘ f) ≡ sumᴮ (sumᴬ ∘ flip f)

record SumProp A : ★₁ where
  constructor mk
  field
    sum : Sum A
    is-linear : SumLinear sum
    sum-ext : SumExt sum
    sum-mon : SumMon sum
    sum-swap : SumSwap sum

  -- open SumLinear is-linear public

  sum-lin = SumLinear.sum-lin is-linear
  sum-hom = SumLinear.sum-hom is-linear

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
μ⊤ = mk sum⊤ (mk sum⊤-lin sum⊤-hom) sum⊤-ext sum⊤-mon sum⊤-swap
  where
    sum⊤-ext : SumExt sum⊤
    sum⊤-ext f≗g = f≗g _

    sum⊤-lin : SumLin sum⊤
    sum⊤-lin f k = refl

    sum⊤-hom : SumHom sum⊤
    sum⊤-hom f g = refl

    sum⊤-mon : SumMon sum⊤
    sum⊤-mon f g f≤°g = f≤°g tt

    sum⊤-swap : SumSwap sum⊤
    sum⊤-swap f sumᴬ-linear = refl

sumBit : Sum Bit
sumBit f = f 0b + f 1b

μBit : SumProp Bit
μBit = mk sumBit (mk sumBit-lin sumBit-hom) sumBit-ext sumBit-mon sumBit-swap
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

    sumBit-mon : SumMon sumBit
    sumBit-mon f g f≤°g = f≤°g 0b +-mono f≤°g 1b

    sumBit-swap : SumSwap sumBit
    sumBit-swap f sumᴬ-linear rewrite SumLinear.sum-hom sumᴬ-linear (f 0b) (f 1b) = refl

infixr 4 _+Sum_

_+Sum_ : ∀ {A B} → Sum A → Sum B → Sum (A ⊎ B)
(sumᴬ +Sum sumᴮ) f = sumᴬ (f ∘ inj₁) + sumᴮ (f ∘ inj₂)

_+μ_ : ∀ {A B} → SumProp A
               → SumProp B
               → SumProp (A ⊎ B)
(μA +μ μB) = mk +-μ (mk +μ-lin +μ-hom) +μ-ext +μ-mon +μ-swap
  where
    +-μ = sum μA +Sum sum μB
    +μ-ext : SumExt +-μ 
    +μ-ext f≗g rewrite sum-ext μA (f≗g ∘ inj₁) | sum-ext μB (f≗g ∘ inj₂) = refl

    +μ-lin : SumLin +-μ
    +μ-lin f k rewrite sum-lin μA (f ∘ inj₁) k | sum-lin μB (f ∘ inj₂) k 
          = sym (proj₁ ℕ°.distrib k (sum μA (f ∘ inj₁)) (sum μB (f ∘ inj₂)))

    +μ-hom : SumHom +-μ
    +μ-hom f g rewrite sum-hom μA (f ∘ inj₁) (g ∘ inj₁) | sum-hom μB (f ∘ inj₂) (g ∘ inj₂)
          = +-interchange (sum μA (f ∘ inj₁)) (sum μA (g ∘ inj₁))
              (sum μB (f ∘ inj₂)) (sum μB (g ∘ inj₂))
          
    +μ-mon : SumMon +-μ
    +μ-mon f g f≤°g = sum-mon μA (f ∘ inj₁) (g ∘ inj₁) (f≤°g ∘ inj₁)
               +-mono sum-mon μB (f ∘ inj₂) (g ∘ inj₂) (f≤°g ∘ inj₂)

    +μ-swap : SumSwap +-μ
    +μ-swap f {sumᴬ} sumᴬ-linear rewrite SumLinear.sum-hom sumᴬ-linear (λ x → sum μA (λ y → f (inj₁ y) x)) (λ x → sum μB (λ y → f (inj₂ y) x))
      | sum-swap μA (f ∘ inj₁) sumᴬ-linear
      | sum-swap μB (f ∘ inj₂) sumᴬ-linear
      = refl

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
   = mk μ-× (mk lin hom) (sum-ext μA ×Sum-ext sum-ext μB) mon ×μ-swap
   where
     μ-× = sum μA ×Sum sum μB

     lin : SumLin μ-×
     lin f k rewrite sum-ext μA (λ x → sum-lin μB (λ y → f (x , y)) k) = sum-lin μA (sum μB ∘ curry f) k

     hom : SumHom μ-×
     hom f g rewrite sum-ext μA (λ x → sum-hom μB (λ y → f (x , y)) (λ y → g (x , y))) 
         = sum-hom μA (sum μB ∘ curry f) (sum μB ∘ curry g)

     mon : SumMon μ-×
     mon f g f≤°g = sum-mon μA (sum μB ∘ curry f) (sum μB ∘ curry g) (λ x → sum-mon μB (curry f x) (curry g x) 
                      (λ x₁ → f≤°g (x , x₁)))

     ×μ-swap : SumSwap μ-×
     ×μ-swap f {sumˣ} sumˣ-linear rewrite sum-ext μA  (λ x → sum-swap μB (curry f x) sumˣ-linear)
       = sum-swap μA (λ z x → sum μB (λ y → f (z , y) x)) sumˣ-linear

sum-0 : ∀ {A} (μA : SumProp A) → sum μA (const 0) ≡ 0
sum-0 μA = sum-lin μA (λ _ → 0) 0

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
sumFin n f = vsum (vmap f (allFin n)) -- or vsum (tabulate f)

μFin : ∀ n → SumProp (Fin n)
μFin n = mk (sumFin n) (mk sumFin-lin sumFin-hom) sumFin-ext sumFin-mon sumFin-swap
  module SumFin where
    sumFin-ext : SumExt (sumFin n)
    sumFin-ext f≗g rewrite map-ext f≗g (allFin n) = refl

    sumFin-lin : SumLin (sumFin n)
    sumFin-lin f x = sum-distribˡ f x (allFin n)
    
    sumFin-hom : SumHom (sumFin n)
    sumFin-hom f g = sum-linear f g (allFin n)

    sumFin-mon : SumMon (sumFin n)
    sumFin-mon f g f≤°g = sum-mono f g f≤°g (allFin n)

    sumFin-swap : SumSwap (sumFin n)
    sumFin-swap f {sumˣ} sumˣ-linear = inner (allFin n) where
      inner : ∀ {m}(xs : Vec (Fin n) m) → vsum (vmap (sumˣ ∘ f) xs) ≡ sumˣ (λ x → vsum (vmap (flip f x) xs))
      inner [] = sym (SumLinear.sum-lin sumˣ-linear (const 1337) 0)
      inner (x ∷ xs) rewrite inner xs = sym
                                          (SumLinear.sum-hom sumˣ-linear (f x)
                                                (λ y → vsum (vmap (flip f y) xs)))

sumVec : ∀ {A} n → Sum A → Sum (Vec A n)
sumVec zero    sumᴬ f = f []
sumVec (suc n) sumᴬ f = sumᴬ (λ x → sumVec n sumᴬ (f ∘ _∷_ x))

μVec : ∀ {A} (μA : SumProp A) n  → SumProp (Vec A n)
μVec {A} μA n = mk (sV n)  (mk (sumVec-lin n) (sumVec-hom n)) (sumVec-ext n) (sumVec-mon n) (sumVec-swap n)
  where
    sV = flip sumVec (sum μA)

    sumVec-ext : ∀ n → SumExt (sV n)
    sumVec-ext zero    f≗g = f≗g []
    sumVec-ext (suc n) f≗g = sum-ext μA (λ x → sumVec-ext n (f≗g ∘ _∷_ x))

    sumVec-lin : ∀ n → SumLin (sV n)
    sumVec-lin zero    f k = refl
    sumVec-lin (suc n) f k rewrite sum-ext μA (λ x → sumVec-lin n (f ∘ _∷_ x) k)
      = sum-lin μA (λ x → sV n (f ∘ _∷_ x)) k

    sumVec-hom : ∀ n → SumHom (sV n)
    sumVec-hom zero    f g = refl
    sumVec-hom (suc n) f g rewrite sum-ext μA (λ x → sumVec-hom n (f ∘ _∷_ x) (g ∘ _∷_ x)) 
      = sum-hom μA (λ x → sV n (f ∘ _∷_ x)) (λ x → sV n (g ∘ _∷_ x))

    sumVec-mon : ∀ n → SumMon (sV n)
    sumVec-mon zero    f g f≤°g = f≤°g []
    sumVec-mon (suc n) f g f≤°g = sum-mon μA (λ x → sV n (f ∘ _∷_ x))
                                             (λ x → sV n (g ∘ _∷_ x)) 
                                    (λ x → sumVec-mon n (f ∘ _∷_ x) (g ∘ _∷_ x) (f≤°g ∘ _∷_ x))

    sumVec-swap : ∀ n → SumSwap (sV n)
    sumVec-swap zero    f        μˣ-linear = refl
    sumVec-swap (suc n) f {sumˣ} μˣ-linear rewrite sum-ext μA (λ x → sumVec-swap n (f ∘ _∷_ x) μˣ-linear)
      = sum-swap μA (λ z x → sumVec n (sum μA) (λ y → f (z ∷ y) x)) μˣ-linear

sumVec-++ : ∀ {A} n {m} (μA : SumProp A)(f : Vec A (n + m)→ ℕ) 
           → sum (μVec μA (n + m)) (λ xs → f xs)
           ≡ sum (μVec μA n) (λ xs → sum (μVec μA m) (λ ys → f (xs ++ ys)))
sumVec-++ zero    μA f = refl
sumVec-++ (suc n) μA f = sum-ext μA (λ x → sumVec-++ n μA (f ∘ _∷_ x))

sumVec-swap : ∀ {A} n {m} (μA : SumProp A)(f : Vec A (n + m) → ℕ)
            → sum (μVec μA n) (λ xs → sum (μVec μA m) (λ ys → f (xs ++ ys)))
            ≡ sum (μVec μA m) (λ ys → sum (μVec μA n) (λ xs → f (xs ++ ys)))
sumVec-swap n {m} μA f = sum-swap (μVec μA n) (λ xs ys → f (xs ++ ys))
                           (is-linear (μVec μA m))


μ-view : ∀ {A B : Set} → (A → B) → SumProp A → SumProp B
μ-view {A}{B} A→B μA = mk sumB (mk μB-lin μB-hom) μB-ext μB-mon μB-swap
  where
    sumB : Sum B
    sumB f = sum μA (f ∘ A→B)

    μB-ext : SumExt sumB
    μB-ext f≗g = sum-ext μA (f≗g ∘ A→B)

    μB-lin : SumLin sumB
    μB-lin f k = sum-lin μA (f ∘ A→B) k

    μB-hom : SumHom sumB
    μB-hom f g = sum-hom μA (f ∘ A→B) (g ∘ A→B)

    μB-mon : SumMon sumB
    μB-mon f g f≤°g = sum-mon μA (f ∘ A→B) (g ∘ A→B) (f≤°g ∘ A→B)

    μB-swap : SumSwap sumB
    μB-swap f {sumˣ} sumˣ-linear = sum-swap μA (f ∘ A→B) sumˣ-linear

μ-view-preserve : ∀ {A B} (A→B : A → B)(B→A : B → A)(A≈B : id ≗ B→A ∘ A→B) f (μA : SumProp A) → sum μA f ≡ sum (μ-view A→B μA) (f ∘ B→A)
μ-view-preserve A→B B→A A≈B f μA = sum-ext μA (cong f ∘ A≈B)

swapS : ∀ {A B} → SumProp (A × B) → SumProp (B × A)
swapS = μ-view Data.Product.swap

swapS-preserve : ∀ {A B} f (μA×B : SumProp (A × B)) → sum μA×B f ≡ sum (swapS μA×B) (f ∘ Data.Product.swap)
swapS-preserve f μA×B =  μ-view-preserve Data.Product.swap Data.Product.swap (λ x → refl) f μA×B {- or refl -}

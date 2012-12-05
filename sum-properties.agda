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
StableUnderInjection μ = ∀ f p → Injective p → sum μ f ≡ sum μ (f ∘ p)

#-StableUnderInjection : ∀ {A}{μ : SumProp A} → StableUnderInjection μ
    → ∀ f p → Injective p → count μ f ≡ count μ (f ∘ p)
#-StableUnderInjection sui f p p-inj = sui (toℕ ∘ f) p p-inj

open import Data.Fin using (Fin ; zero ; suc)

record Finable {A : Set}(μA : SumProp A) : Set where
  constructor mk
  field
    FinCard  : ℕ
    toFin    : A → Fin (suc FinCard)
    fromFin  : Fin (suc FinCard) → A
    to-inj   : Injective toFin
    from-inj : Injective fromFin
    iso      : fromFin ∘ toFin ≗ id
    sums-ok  : ∀ f → sum μA f ≡ sum (μFin FinCard) (f ∘ fromFin)

postulate
  Fin-Stab : ∀ n → StableUnderInjection (μFin n)

⊤-Finable : Finable μ⊤
⊤-Finable = mk 0 (λ x → zero) (λ x → _) (λ x₁ → ≡.refl) (λ x₁ → help) (λ x → ≡.refl) (λ f → ≡.refl) 
  where help : {x y : Fin 1} → x ≡ y
        help {zero} {zero} = ≡.refl
        help {zero} {suc ()}
        help {suc ()}

+-Finable : ∀ {A B}(μA : SumProp A)(μB : SumProp B) → Finable μA → Finable μB → Finable (μA +μ μB)
+-Finable {A}{B} μA μB finA finB = mk FinCard toFin fromFin to-inj from-inj iso sums-ok where
    open import Data.Sum
    open import Data.Empty

    |A| = suc (Finable.FinCard finA)
    |B| = suc (Finable.FinCard finB)

    Fsuc-injective : ∀ {n} {i j : Fin n} → Fin.suc i ≡ suc j → i ≡ j
    Fsuc-injective ≡.refl = ≡.refl
    
    inj₁-inj : ∀ {A B : Set} {x y : A} → inj₁ {B = B} x ≡ inj₁ y → x ≡ y
    inj₁-inj ≡.refl = ≡.refl

    inj₂-inj : ∀ {A B : Set} {x y : B} → inj₂ {A = A} x ≡ inj₂ y → x ≡ y
    inj₂-inj ≡.refl = ≡.refl

    fin₁ : ∀ n {m} → Fin n → Fin (n + m)
    fin₁ zero ()
    fin₁ (suc n) zero = zero
    fin₁ (suc n) (suc i) = suc (fin₁ n i)

    fin₂ : ∀ n {m} → Fin m → Fin (n + m)
    fin₂ zero i = i
    fin₂ (suc n) i = suc (fin₂ n i)

    toFin' : ∀ {n} {m} → Fin n ⊎ Fin m → Fin (n + m)
    toFin' {n} (inj₁ x) = fin₁ n x
    toFin' {n} (inj₂ y) = fin₂ n y

    fin₁-inj : ∀ n {m} → Injective (fin₁ n {m})
    fin₁-inj .(suc n) {m} {zero {n}} {zero} x≡y = ≡.refl
    fin₁-inj .(suc n) {m} {zero {n}} {suc y} ()
    fin₁-inj .(suc n) {m} {suc {n} x} {zero} ()
    fin₁-inj .(suc n) {m} {suc {n} x} {suc y} x≡y = ≡.cong suc (fin₁-inj n (Fsuc-injective x≡y))

    fin₂-inj : ∀ n {m} → Injective (fin₂ n {m})
    fin₂-inj zero eq = eq
    fin₂-inj (suc n) eq = fin₂-inj n (Fsuc-injective eq)

    fin₁≠fin₂ : ∀ n {m} x y → (fin₁ n {m} x ≡ fin₂ n y) → ⊥
    fin₁≠fin₂ .(suc n) (zero {n}) zero ()
    fin₁≠fin₂ .(suc n) (zero {n}) (suc y) ()
    fin₁≠fin₂ .(suc n) (suc {n} x) zero eq = fin₁≠fin₂ n x zero (Fsuc-injective eq)
    fin₁≠fin₂ .(suc n) (suc {n} x) (suc y) eq = fin₁≠fin₂ n x (suc y) (Fsuc-injective eq)

    fromFin' : ∀ n {m} → Fin (n + m) → Fin n ⊎ Fin m
    fromFin' zero k = inj₂ k
    fromFin' (suc n) zero = inj₁ zero
    fromFin' (suc n) (suc k) with fromFin' n k
    ... | inj₁ x = inj₁ (suc x)
    ... | inj₂ y = inj₂ y

    fromFin'-inj : ∀ n {m} x y → fromFin' n {m} x ≡ fromFin' n y → x ≡ y
    fromFin'-inj zero x y eq = inj₂-inj eq
    fromFin'-inj (suc n) zero zero eq = ≡.refl
    fromFin'-inj (suc n) zero (suc y) eq = {!!}
    fromFin'-inj (suc n) (suc x) zero eq = {!!}
    fromFin'-inj (suc n) (suc x) (suc y) eq = {!fromFin'-inj n x y!}

    fromFin'-inj₁ : ∀ n {m} x → fromFin' n {m} (fin₁ n x) ≡ inj₁ x
    fromFin'-inj₁ zero ()
    fromFin'-inj₁ (suc n) zero = ≡.refl
    fromFin'-inj₁ (suc n) {m} (suc x) rewrite fromFin'-inj₁ n {m} x  = ≡.refl

    fromFin'-inj₂ : ∀ n {m} x → fromFin' n {m} (fin₂ n x) ≡ inj₂ x
    fromFin'-inj₂ zero x = ≡.refl
    fromFin'-inj₂ (suc n) x rewrite fromFin'-inj₂ n x = ≡.refl

    FinCard  : ℕ
    FinCard = Finable.FinCard finA + suc (Finable.FinCard finB)

    toFin    : A ⊎ B → Fin (suc FinCard)
    toFin (inj₁ x) = toFin' (inj₁ (Finable.toFin finA x))
    toFin (inj₂ y) = toFin' {n = |A|} (inj₂ (Finable.toFin finB y))

    fromFin  : Fin (suc FinCard) → A ⊎ B
    fromFin x+y with fromFin' |A| x+y
    ... | inj₁ x = inj₁ (Finable.fromFin finA x)
    ... | inj₂ y = inj₂ (Finable.fromFin finB y)

    to-inj   : Injective toFin
    to-inj {inj₁ x} {inj₁ x₁} tx≡ty = ≡.cong inj₁ (Finable.to-inj finA (fin₁-inj |A| tx≡ty))
    to-inj {inj₁ x} {inj₂ y} tx≡ty = ⊥-elim (fin₁≠fin₂ |A| _ _ tx≡ty)
    to-inj {inj₂ y} {inj₁ x} tx≡ty = ⊥-elim (fin₁≠fin₂ |A| _ _ (≡.sym tx≡ty))
    to-inj {inj₂ y} {inj₂ y₁} tx≡ty = ≡.cong inj₂ (Finable.to-inj finB (fin₂-inj |A| tx≡ty))

    from-inj : Injective fromFin
    from-inj {x} {y} fx≡fy = {!!}

    iso      : fromFin ∘ toFin ≗ id
    iso (inj₁ x) rewrite fromFin'-inj₁ |A| {|B|} (Finable.toFin finA x) | Finable.iso finA x = ≡.refl
    iso (inj₂ y) rewrite fromFin'-inj₂ |A| {|B|} (Finable.toFin finB y) | Finable.iso finB y = ≡.refl

    sums-ok  : ∀ f → sum (μA +μ μB) f ≡ sum (μFin FinCard) (f ∘ fromFin)
    sums-ok f =
        sum (μA +μ μB) f
      ≡⟨ ≡.cong₂ _+_ (Finable.sums-ok finA (f ∘ inj₁))
           (Finable.sums-ok finB (f ∘ inj₂)) ⟩
        sum (μFin (Finable.FinCard finA)) (f ∘ inj₁ ∘ Finable.fromFin finA)
      + sum (μFin (Finable.FinCard finB)) (f ∘ inj₂ ∘ Finable.fromFin finB)
      ≡⟨ {!!} ⟩
        sum (μFin FinCard) (f ∘ fromFin)
      ∎
      where open ≡.≡-Reasoning

StableIfFinable : ∀ {A} (μA : SumProp A) → Finable μA → StableUnderInjection μA
StableIfFinable μA fin f p p-inj
  = sum μA f
  ≡⟨ sums-ok f ⟩
    sum (μFin FinCard) (f ∘ fromFin)
  ≡⟨ Fin-Stab FinCard (f ∘ fromFin) (toFin ∘ p ∘ fromFin) (from-inj ∘ p-inj ∘ to-inj) ⟩
    sum (μFin FinCard) (f ∘ fromFin ∘ toFin ∘ p ∘ fromFin)
  ≡⟨ sum-ext (μFin FinCard) (λ x → ≡.cong f (iso (p (fromFin x)))) ⟩
    sum (μFin FinCard) (f ∘ p ∘ fromFin)
  ≡⟨ ≡.sym (sums-ok (f ∘ p)) ⟩
    sum μA (f ∘ p)
  ∎
  where open ≡.≡-Reasoning
        open Finable fin


module _ where
  open import bijection-fin
  open import Data.Vec.NP

  sumFinSUI : ∀ n f p → Injective p → sumFin n f ≡ sumFin n (f ∘ p)
  sumFinSUI n f p p-inj = count-perm f p (λ x y → p-inj)

  μFinSUI : ∀ {n} → StableUnderInjection (μFin n)
  μFinSUI {n} f p p-inj rewrite ≡.sym (sumFin-spec n f)
                              | ≡.sym (sumFin-spec n (f ∘ p))
                              = sumFinSUI (suc n) f p p-inj


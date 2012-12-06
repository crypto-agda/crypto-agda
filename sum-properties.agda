module sum-properties where

open import Type

import Level as L

open import Data.Empty using (⊥)

open import Data.Bool.NP
open import Data.Nat.NP
open import Data.Nat.Properties

open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤)

open import Function.NP
import Function.Inverse as Inv
open Inv using (_↔_)
open import Function.Related
open import Function.Related.TypeIsomorphisms.NP
open import Function.Equality using (_⟨$⟩_)

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

  FIN = Fin (suc FinCard)

  field
    iso      : A ↔ Fin (suc FinCard)
    
  toFin : A → FIN
  toFin x = Inv.Inverse.to iso ⟨$⟩ x

  fromFin : FIN → A
  fromFin x = Inv.Inverse.from iso ⟨$⟩ x

  field
    sums-ok  : ∀ f → sum μA f ≡ sum (μFinSuc FinCard) (f ∘ fromFin)

  from-inj : Injective fromFin
  from-inj = Inv.Inverse.injective (Inv.sym iso)

  to-inj : Injective toFin
  to-inj = Inv.Inverse.injective iso

  iso' : fromFin ∘ toFin ≗ id
  iso' = Inv.Inverse.left-inverse-of iso

⊤-Finable : Finable μ⊤
⊤-Finable = mk 0 iso sums-ok where

  iso : _
  iso = ⊤ ↔⟨ sym A⊎⊥↔A ⟩
        (⊤ ⊎ ⊥) ↔⟨ Inv.id ⊎-cong sym Fin0↔⊥ ⟩
        (⊤ ⊎ Fin 0) ↔⟨ sym Fin∘suc↔⊤⊎Fin ⟩
        Fin (suc 0) ∎
    where open EquationalReasoning
          open import Relation.Binary.Sum

  sums-ok : (_ : _) → _
  sums-ok f = ≡.refl

+-Finable : ∀ {A B}(μA : SumProp A)(μB : SumProp B) → Finable μA → Finable μB → Finable (μA +μ μB)
+-Finable {A}{B} μA μB finA finB = mk FinCard iso sums-ok where

  |A| |B| : ℕ
  |A| = suc (Finable.FinCard finA)
  |B| = suc (Finable.FinCard finB)

  μFinA = μFinSuc (Finable.FinCard finA)
  μFinB = μFinSuc (Finable.FinCard finB)

  FinCard : _
  FinCard = Finable.FinCard finA + |B|

  iso : _
  iso = (A ⊎ B) 
      ↔⟨ (Finable.iso finA) ⊎-cong (Finable.iso finB) ⟩ 
        (Fin |A| ⊎ Fin |B|)
      ↔⟨ Fin-⊎-+ |A| |B| ⟩
        Fin (|A| + |B|)
      ∎
    where 
      open import Relation.Binary.Sum
      open EquationalReasoning

  from : ∀ {A B : Set} → A ↔ B → B → A
  from iso x = Inv.Inverse.from iso ⟨$⟩ x

  to : ∀ {A B : Set} → A ↔ B → A → B
  to iso x = Inv.Inverse.to iso ⟨$⟩ x

  fromFin : Fin (|A| + |B|) → A ⊎ B
  fromFin x = from iso x
  
  open import Data.Vec.NP using (Vec ; foldr₁ ; tabulate-ext)
  vsum : ∀ {n} → Vec ℕ (suc n) → ℕ
  vsum = foldr₁ _+_

  fin-proof : ∀ n m (f : Fin (suc n) ⊎ Fin (suc m) → ℕ) → 
                      sum (μFinSuc n) (f ∘ inj₁) 
                    + sum (μFinSuc m) (f ∘ inj₂) 
                    ≡ sum (μFinSuc (n + suc m)) (f ∘ from  (Fin-⊎-+ (suc n) (suc m)))
  fin-proof zero m f    rewrite tabulate-ext (≡.cong (f ∘ inj₂ ∘ suc) ∘ ≡.sym ∘ Inv.Inverse.right-inverse-of (Maybe^⊥↔Fin m)) = ≡.refl
  fin-proof (suc n) m f = sum (μFinSuc (suc n)) (f ∘ inj₁) + sum (μFinSuc m) (f ∘ inj₂) 
                        ≡⟨ ℕ°.+-assoc (f (inj₁ zero)) (sum (μFinSuc n) (f ∘ inj₁ ∘ suc)) (sum (μFinSuc m) (f ∘ inj₂)) ⟩ 
                          f (inj₁ zero) + (sum (μFinSuc n) (f ∘ inj₁ ∘ suc) + sum (μFinSuc m) (f ∘ inj₂))
                        ≡⟨ ≡.cong (_+_ (f (inj₁ zero))) (fin-proof n m (F f)) ⟩
                          f (inj₁ zero) + sum (μFinSuc (n + suc m)) (F f ∘ from (Fin-⊎-+ (suc n) (suc m)))
                        ≡⟨ ≡.cong (_+_ (f (inj₁ zero))) (sum-ext (μFinSuc (n + suc m)) (F-proof (suc n) (suc m) f)) ⟩
                          f (inj₁ zero) + sum (μFinSuc (n + suc m)) (f ∘ from (Fin-⊎-+ (suc (suc n)) (suc m)) ∘ suc)
                        ≡⟨ ≡.refl ⟩
                          sum (μFinSuc (suc n + suc m))
                                     (f ∘ from (Fin-⊎-+ (suc (suc n)) (suc m))) 
                        ∎
    where 
      open ≡.≡-Reasoning
      F : ∀ {n m} → (Fin (suc n) ⊎ Fin m → ℕ) → Fin n ⊎ Fin m → ℕ
      F f = [ (f ∘ inj₁ ∘ suc) , (f ∘ inj₂) ]


      F-proof : ∀ n m f → F f ∘ from (Fin-⊎-+ n m) ≗ f ∘ from (Fin-⊎-+ (suc n) m) ∘ suc
      F-proof n m f x with (Inv.Inverse.from (Maybe^-⊎-+ n m) ⟨$⟩ (Inv.Inverse.from (Maybe^⊥↔Fin (n + m)) ⟨$⟩ x))
      ... | inj₁ y = ≡.refl
      ... | inj₂ y = ≡.refl

  sums-ok : (_ : _) → _
  sums-ok f = sum (μA +μ μB) f
            ≡⟨ ≡.cong₂ _+_ (Finable.sums-ok finA (f ∘ inj₁)) (Finable.sums-ok finB (f ∘ inj₂)) ⟩
              sum μFinA (f ∘ inj₁ ∘ from (Finable.iso finA))
            + sum μFinB (f ∘ inj₂ ∘ from (Finable.iso finB))
            ≡⟨ ≡.cong₂ _+_ (sum-ext μFinA {f = f ∘ inj₁ ∘ from (Finable.iso finA)} (λ x → ≡.refl)) 
                           (sum-ext μFinB {f = f ∘ inj₂ ∘ from (Finable.iso finB)} (λ _ → ≡.refl)) ⟩ 
              sum μFinA (f ∘ from F ∘ inj₁)
            + sum μFinB (f ∘ from F ∘ inj₂)
            ≡⟨ fin-proof _ _ (f ∘ from F) ⟩
              sum (μFinSuc FinCard) (f ∘ from F ∘ from (Fin-⊎-+ |A| |B|))
            ≡⟨ ≡.refl ⟩
              sum (μFinSuc FinCard) (f ∘ from iso) 
            ∎
    where
      open ≡.≡-Reasoning
      open import Relation.Binary.Sum
      F :  (A ⊎ B) ↔ (Fin |A| ⊎ Fin |B|)
      F = Finable.iso finA ⊎-cong Finable.iso finB

×-Finable : ∀ {A B}(μA : SumProp A)(μB : SumProp B) → Finable μA → Finable μB → Finable (μA ×μ μB)
×-Finable {A} {B} μA μB finA finB = mk FinCard iso sums-ok where
  |A| |B| : ℕ
  |A| = suc (Finable.FinCard finA)
  |B| = suc (Finable.FinCard finB)

  μFinA = μFinSuc (Finable.FinCard finA)
  μFinB = μFinSuc (Finable.FinCard finB)

  FinCard = Finable.FinCard finB + Finable.FinCard finA * |B|

  prf : suc FinCard ≡ |A| * |B|
  prf = ≡.refl

  iso : _
  iso = (A × B) ↔⟨ (Finable.iso finA) ×-cong (Finable.iso finB) ⟩ 
        (Fin |A| × Fin |B|) ↔⟨ {!!} ⟩
        Fin (|A| * |B|) ∎
    where open EquationalReasoning
          open import Relation.Binary.Product.Pointwise

  sums-ok : (_ : _) → _
  sums-ok f = {!!}

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
  μFinSUI {n} f p p-inj rewrite ≡.sym (sumFin-spec n f)
                              | ≡.sym (sumFin-spec n (f ∘ p))
                              = sumFinSUI (suc n) f p p-inj

StableIfFinable : ∀ {A} (μA : SumProp A) → Finable μA → StableUnderInjection μA
StableIfFinable μA fin f p p-inj
  = sum μA f
  ≡⟨ sums-ok f ⟩
    sum (μFinSuc FinCard) (f ∘ fromFin)
  ≡⟨ μFinSUI (f ∘ fromFin) (toFin ∘ p ∘ fromFin) (from-inj ∘ p-inj ∘ to-inj) ⟩
    sum (μFinSuc FinCard) (f ∘ fromFin ∘ toFin ∘ p ∘ fromFin)
  ≡⟨ sum-ext (μFinSuc FinCard) (λ x → ≡.cong f (iso' (p (fromFin x)))) ⟩
    sum (μFinSuc FinCard) (f ∘ p ∘ fromFin)
  ≡⟨ ≡.sym (sums-ok (f ∘ p)) ⟩
    sum μA (f ∘ p)
  ∎
  where open ≡.≡-Reasoning
        open Finable fin


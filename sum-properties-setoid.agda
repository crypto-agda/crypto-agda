module sum-properties-setoid where

open import Type
import Level as L

open import Algebra
import Algebra.FunctionProperties as FP

open import Data.Empty using (⊥)
open import Data.Bool.NP
open Data.Bool.NP.Indexed
open import Data.Fin using (Fin)
open import Data.Nat.NP
open import Data.Nat.Properties
open import Data.Product renaming (map to pmap)
open import Data.Sum
open import Data.Unit using (⊤)
open import Function.NP
import Function.Inverse as Inv
open Inv using (_↔_)
open import Function.Related
open import Function.Related.TypeIsomorphisms.NP

import Function.Equality as FE
open FE using (_⟨$⟩_)

import Function.Injection as FInj

open import sum-setoid

open import Relation.Binary
open import Relation.Binary.Sum.NP
open import Relation.Binary.Product.Pointwise
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

Injectivoid : ∀ {A B : SEToid} → (Setoid.Carrier A → Setoid.Carrier B) → Set
Injectivoid {A}{B} f = ∀ {x y} → Setoid._≈_ B (f x) (f y) → Setoid._≈_ A x y

StableUnderInjection : ∀ {A} → SumPropoid A → Set
StableUnderInjection {A} μ = ∀ p → SumStableUnder μ (FInj.Injection.to p)

CountStableUnderInjection : ∀ {A} → SumPropoid A → Set
CountStableUnderInjection μ = ∀ p → CountStableUnder μ (FInj.Injection.to p)

{-
#-StableUnderInjection : ∀ {A}{μ : SumPropoid A} → StableUnderInjection μ
    → ∀ f p → Injective p → count μ f ≡ count μ (f ∘ p)
#-StableUnderInjection sui f p p-inj = {!sui p p-inj (toℕ ∘ f)!}
-}

sum$ : ∀ {As} → SumPropoid As → (As FE.⟶ ≡.setoid ℕ) → ℕ
sum$ μA f = sum μA (_⟨$⟩_ f)

infix 4 _≈_ -- _≈'_



record _≈_ {As Bs : SEToid}(μA : SumPropoid As)(μB : SumPropoid Bs): Set where
  constructor mk
  field
    iso : Inv.Inverse As Bs
  
  private
    A = Setoid.Carrier As
    B = Setoid.Carrier Bs

  from : Bs FE.⟶ As
  from = Inv.Inverse.from iso

  from$ : B → A
  from$ = _⟨$⟩_ from

  to : As FE.⟶ Bs
  to = Inv.Inverse.to iso

  to$ : A → B
  to$ = _⟨$⟩_ to

  from-inj : FInj.Injection Bs As -- Injectivoid {Bs} {As} from$
  from-inj = Inv.Inverse.injection (Inv.sym iso)

  to-inj : FInj.Injection As Bs -- Injectivoid {As} {Bs} to$
  to-inj = Inv.Inverse.injection iso


  field
    sums-ok : ∀ f → sum$ μA f ≡ sum$ μB (f FE.∘ from)

  sums-ok' : ∀ f → sum$ μB f ≡ sum$ μA (f FE.∘ to)
  sums-ok' f
             = sum$ μB f
             ≡⟨ search-extoid μB _+_ {f = f}
                  {g = f FE.∘ to FE.∘ from}
                  (λ {x}{y} x≈y → FE.cong f (SB.trans x≈y (SB.sym (Inv.Inverse.right-inverse-of iso y)))) ⟩
               sum$ μB (f FE.∘ to FE.∘ from)
             ≡⟨ ≡.sym (sums-ok (f FE.∘ to)) ⟩
               sum$ μA (f FE.∘ to)
             ∎
    where open ≡.≡-Reasoning
          module SB = Setoid Bs
          module SA = Setoid As



  StableUnder≈ : StableUnderInjection μA → StableUnderInjection μB
  StableUnder≈ μA-SUI p f
    = sum$ μB f
    ≡⟨ sums-ok' f ⟩
      sum$ μA (f FE.∘ to)
    ≡⟨ μA-SUI (from-inj FInj.∘ p FInj.∘ to-inj) (f FE.∘ to) ⟩
      sum$ μA (f FE.∘ to FE.∘ from FE.∘ FInj.Injection.to p FE.∘ to)
    ≡⟨ ≡.sym (sums-ok' (f FE.∘ to FE.∘ from FE.∘ FInj.Injection.to p)) ⟩
      sum$ μB (f FE.∘ to FE.∘ from FE.∘ FInj.Injection.to p)
    ≡⟨ search-extoid μB _+_
         {f = f FE.∘ to FE.∘ from FE.∘ FInj.Injection.to p}
         {g = f FE.∘ FInj.Injection.to p} (FE.cong f ∘ Setoid.trans Bs (Inv.Inverse.right-inverse-of iso _) ∘ FE.cong (FInj.Injection.to p)) ⟩
      sum$ μB (f FE.∘ FInj.Injection.to p)
    ∎
    where open ≡.≡-Reasoning

_≈'_ : ∀ {A B} (μA : SumProp A)(μB : SumProp B) → Set
_≈'_ = _≈_

≈-refl : ∀ {A} (μA : SumPropoid A) → μA ≈ μA
≈-refl μA = mk Inv.id (λ f → ≡.refl)

≈-id : ∀ {A} {μA : SumPropoid A} → μA ≈ μA
≈-id = ≈-refl _

≈-sym : ∀ {A B}{μA : SumPropoid A}{μB : SumPropoid B} → μA ≈ μB → μB ≈ μA
≈-sym A≈B = mk (Inv.sym iso) sums-ok'
  where open _≈_ A≈B

≈-trans : ∀ {A B C}{μA : SumPropoid A}{μB : SumPropoid B}{μC : SumPropoid C} → μA ≈ μB → μB ≈ μC → μA ≈ μC
≈-trans A≈B B≈C = mk (iso B≈C Inv.∘ iso A≈B) (λ f → ≡.trans (sums-ok A≈B f) (sums-ok B≈C (f FE.∘ from A≈B)))
  where open _≈_

infix 2 _≈∎
infixr 2 _≈⟨_⟩_

_≈∎ : ∀ {A} (μA : SumPropoid A) → μA ≈ μA
_≈∎ = ≈-refl

_≈⟨_⟩_ : ∀ {A B C} (μA : SumPropoid A){μB : SumPropoid B}{μC : SumPropoid C} → μA ≈ μB → μB ≈ μC → μA ≈ μC
_ ≈⟨ A≈B ⟩ B≈C = ≈-trans A≈B B≈C

lift-⊎ : ∀ {A B : Set} → Inv.Inverse (≡.setoid (A ⊎ B)) ((≡.setoid A) ⊎-setoid (≡.setoid B))
lift-⊎ {A} {B} =  record { to = to; from = from; inverse-of = inverse-of } where
  to : _
  to = record { _⟨$⟩_ = id; cong = cong } where
    cong : ∀ {i j} → i ≡ j → _
    cong ≡.refl = Setoid.refl (≡.setoid (A) ⊎-setoid (≡.setoid B))

  from : _
  from = record { _⟨$⟩_ = id; cong = cong } where
    cong : ∀ {i j} → ⊎ʳ ⊥ _≡_ _≡_ i j → i ≡ j
    cong (₁∼₂ ())
    cong (₁∼₁ x∼₁y) = ≡.cong inj₁ x∼₁y
    cong (₂∼₂ x∼₂y) = ≡.cong inj₂ x∼₂y

  inverse-of : _
  inverse-of = record { left-inverse-of = left-inverse-of; right-inverse-of = right-inverse-of } where
   left-inverse-of : (_ : _) → _
   left-inverse-of  x = Setoid.refl (≡.setoid (A ⊎ B))

   right-inverse-of : (_ : _) → _
   right-inverse-of x = Setoid.refl ((≡.setoid A) ⊎-setoid (≡.setoid B))

Fin0≈⊤ : μFinSuc zero ≈ μ⊤
Fin0≈⊤ = mk iso sums-ok where
  open import Relation.Binary.Sum
  iso : _
  iso = (A⊎⊥↔A Inv.∘ Inv.id ⊎-cong Fin0↔⊥) Inv.∘ Fin∘suc↔⊤⊎Fin

  sums-ok : (_ : _) → _
  sums-ok f = ≡.refl


⊤+Fin : ∀ {n} → μ⊤ +μ μFinSuc n ≈ μFinSuc (suc n)
⊤+Fin {n} = mk iso sums-ok where
  iso : _
  iso = Inv.sym (Inv._∘_ (lift-⊎ {⊤} {Fin (suc n)}) Fin∘suc↔⊤⊎Fin)

  sums-ok : (_ : _) → _
  sums-ok f = ≡.refl

⊤×A≈A : ∀ {A}{μA : SumProp A} → μ⊤ ×μ μA ≈ μA
⊤×A≈A {A} = mk iso sums-ok where
  iso : _
  iso = ×-ICMon.identityˡ _

  sums-ok : (_ : _) → _
  sums-ok f = ≡.refl

μFinPres : ∀ {m n} → m ≡ n → μFinSuc m ≈ μFinSuc n
μFinPres eq rewrite eq = ≈-refl _

_+μ-cong_ : ∀ {A B C D}{μA : SumPropoid A}{μB : SumPropoid B}{μC : SumPropoid C}{μD : SumPropoid D}
          → μA ≈ μC → μB ≈ μD → μA +μ μB ≈ μC +μ μD
A≈C +μ-cong B≈D = mk iso sums-ok where
  iso : _
  iso = (_≈_.iso A≈C) ⊎-inverse (_≈_.iso B≈D) -- (_≈_.iso A≈C) ⊎-cong (_≈_.iso B≈D)

  sums-ok : (_ : _) → _
  sums-ok f = ≡.cong₂ _+_ (_≈_.sums-ok A≈C (f FE.∘ inj₁-setoid)) -- (λ x≈y → f-resp (₁∼₁ x≈y)))
                          (_≈_.sums-ok B≈D (f FE.∘ inj₂-setoid)) -- (λ x≈y → f-resp (₂∼₂ x≈y)))

+μ-assoc : ∀ {A B C}(μA : SumPropoid A)(μB : SumPropoid B)(μC : SumPropoid C)
         → (μA +μ μB) +μ μC ≈ μA +μ (μB +μ μC)
+μ-assoc μA μB μC = mk iso sums-ok where
  iso : _
  iso = ⊎-ICMon.assoc _ _ _

  sums-ok : (_ : _) → _
  sums-ok f = ℕ°.+-assoc (sum μA (_⟨$⟩_ f ∘ inj₁ ∘ inj₁)) (sum μB (_⟨$⟩_ f ∘ inj₁ ∘ inj₂)) (sum μC (_⟨$⟩_ f ∘ inj₂))


+μ-comm : ∀ {A B}(μA : SumPropoid A)(μB : SumPropoid B)
        → μA +μ μB ≈ μB +μ μA
+μ-comm μA μB = mk iso sums-ok where
  iso : _
  iso = ⊎-ICMon.comm _ _

  sums-ok : (_ : _) → _
  sums-ok f = ℕ°.+-comm (sum$ μA (f FE.∘ inj₁-setoid)) (sum$ μB (f FE.∘ inj₂-setoid))

_×μ-cong_ :  ∀ {A B C D}{μA : SumPropoid A}{μB : SumPropoid B}{μC : SumPropoid C}{μD : SumPropoid D}
          → μA ≈ μC → μB ≈ μD → μA ×μ μB ≈ μC ×μ μD
_×μ-cong_ {A}{B}{C}{D}{μA}{μB}{μC}{μD} A≈C B≈D = mk iso sums-ok where
  open import Relation.Binary.Product.Pointwise
  iso : _
  iso = _≈_.iso A≈C ×-inverse _≈_.iso B≈D

  sums-ok : (_ : (A ×-setoid B) FE.⟶ ≡.setoid ℕ) → _
  sums-ok f = sum$ (μA ×μ μB) f
            ≡⟨ sum-ext μA (λ xa → _≈_.sums-ok B≈D (record
               { _⟨$⟩_ = λ x → f ⟨$⟩ (xa , x)
               ; cong = λ x → FE.cong f (Setoid.refl A , x) })) ⟩
              sum$ (μA ×μ μD) (f FE.∘ FE.id {A = A} ×-⟶ _≈_.from B≈D)
            ≡⟨ _≈_.sums-ok A≈C (record { _⟨$⟩_ = _; cong = λ x → search-ext μD _+_ (λ y → FE.cong f (x , Setoid.refl B)) }) ⟩
              sum$ (μC ×μ μD) (f FE.∘ Inv.Inverse.from iso)
            ∎ where open ≡.≡-Reasoning
   
×μ-assoc : ∀ {A B C}(μA : SumPropoid A)(μB : SumPropoid B)(μC : SumPropoid C)
         → (μA ×μ μB) ×μ μC ≈ μA ×μ (μB ×μ μC)
×μ-assoc {A}{B}{C} μA μB μC = mk iso sums-ok where
  iso : _
  iso = ×-ICMon.assoc A B C

  sums-ok : (_ : _) → _
  sums-ok f = ≡.refl

×μ-comm : ∀ {A B}(μA : SumPropoid A)(μB : SumPropoid B)
        → μA ×μ μB ≈ μB ×μ μA
×μ-comm {A}{B} μA μB = mk iso sums-ok where
  iso : _
  iso = ×-ICMon.comm A B

  sums-ok : (_ : _) → _
  sums-ok f = sum-swap μA μB (curry (_⟨$⟩_ f))


×+-distrib : ∀ {A B C}(μA : SumPropoid A)(μB : SumPropoid B)(μC : SumPropoid C)
           → (μA +μ μB) ×μ μC ≈ (μA ×μ μC) +μ (μB ×μ μC)
×+-distrib {A}{B}{C} μA μB μC = mk iso sums-ok where
  iso : _
  iso = ×⊎°I.distribʳ C A B

  sums-ok : (_ : _) → _
  sums-ok f = ≡.refl

+-≈ : ∀ m n → (μFinSuc m) +μ (μFinSuc n) ≈ μFinSuc (m + suc n)
+-≈ zero n    = μFinSuc zero +μ μFinSuc n
              ≈⟨ Fin0≈⊤ +μ-cong ≈-refl (μFinSuc n) ⟩
                μ⊤ +μ μFinSuc n
              ≈⟨ ⊤+Fin ⟩
                μFinSuc (suc n)
              ≈∎
+-≈ (suc m) n = μFinSuc (suc m) +μ μFinSuc n
              ≈⟨ ≈-sym ⊤+Fin +μ-cong ≈-refl (μFinSuc n) ⟩
                (μ⊤ +μ μFinSuc m) +μ μFinSuc n
              ≈⟨ +μ-assoc μ⊤ (μFinSuc m) (μFinSuc n) ⟩
                μ⊤ +μ (μFinSuc m +μ μFinSuc n)
              ≈⟨ ≈-refl μ⊤ +μ-cong +-≈ m n ⟩
                μ⊤ +μ μFinSuc (m + suc n)
              ≈⟨ ⊤+Fin ⟩
                μFinSuc (suc m + suc n)
              ≈∎

×-≈ : ∀ m n → μFinSuc m ×μ μFinSuc n ≈ μFinSuc (n + m * suc n)
×-≈ zero n    = μFinSuc 0 ×μ μFinSuc n
              ≈⟨ Fin0≈⊤ ×μ-cong (≈-refl (μFinSuc n)) ⟩
                μ⊤ ×μ μFinSuc n
              ≈⟨ ⊤×A≈A ⟩
                μFinSuc n
              ≈⟨ μFinPres (ℕ°.+-comm 0 n) ⟩
                μFinSuc (n + 0)
              ≈∎
×-≈ (suc m) n = μFinSuc (suc m) ×μ μFinSuc n
              ≈⟨ ≈-sym ⊤+Fin ×μ-cong ≈-refl (μFinSuc n) ⟩
                (μ⊤ +μ μFinSuc m) ×μ μFinSuc n
              ≈⟨ ×+-distrib μ⊤ (μFinSuc m) (μFinSuc n) ⟩
                (μ⊤ ×μ μFinSuc n) +μ (μFinSuc m ×μ μFinSuc n)
              ≈⟨ ⊤×A≈A {μA = μFinSuc n} +μ-cong ×-≈ m n ⟩
                μFinSuc n +μ μFinSuc (n + m * suc n)
              ≈⟨ +-≈ n (n + m * suc n) ⟩
                μFinSuc (n + suc m * suc n)
              ≈∎

open import Data.Fin using (Fin ; zero ; suc)

Finable : ∀ {A} → SumPropoid A → Set
Finable μA = Σ ℕ λ FinCard → μA ≈ μFinSuc FinCard

⊤-Finable : Finable μ⊤
⊤-Finable = 0 , ≈-sym Fin0≈⊤

Fin-Finable : ∀ {n} → Finable (μFinSuc n)
Fin-Finable {n} = n , ≈-refl (μFinSuc n)

+-Finable : ∀ {A B}(μA : SumPropoid A)(μB : SumPropoid B) → Finable μA → Finable μB → Finable (μA +μ μB)
+-Finable μA μB (|A| , A≈) (|B| , B≈) = (|A| + suc |B|) ,
  ( μA +μ μB
  ≈⟨ A≈ +μ-cong B≈ ⟩
    μFinSuc |A| +μ μFinSuc |B|
  ≈⟨ +-≈ |A| |B| ⟩
    μFinSuc (|A| + suc |B|) ≈∎)

×-Finable : ∀ {A B}(μA : SumPropoid A)(μB : SumPropoid B) → Finable μA → Finable μB → Finable (μA ×μ μB)
×-Finable μA μB (|A| , A≈) (|B| , B≈) = (|B| + |A| * suc |B|) ,
  ( μA ×μ μB
  ≈⟨ A≈ ×μ-cong B≈ ⟩
    μFinSuc |A| ×μ μFinSuc |B|
  ≈⟨ ×-≈ |A| |B| ⟩
    μFinSuc (|B| + |A| * suc |B|)
  ≈∎)

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
  sumFinSUI n f p p-inj = count-perm f p (λ _ _ → p-inj)

  μFinSUI : ∀ {n} → StableUnderInjection (μFinSuc n)
  μFinSUI {n} p f
    rewrite ≡.sym (sumFin-spec n (_⟨$⟩_ f))
          | ≡.sym (sumFin-spec n (_⟨$⟩_ (f FE.∘ FInj.Injection.to p)))
          = sumFinSUI (suc n) (_⟨$⟩_ f) (_⟨$⟩_ (FInj.Injection.to p)) (FInj.Injection.injective p)

StableIfFinable : ∀ {A} (μA : SumProp A) → Finable μA → StableUnderInjection μA
StableIfFinable μA (_ , A≈Fin)
  = _≈_.StableUnder≈ (≈-sym A≈Fin) μFinSUI

-- -}
-- -}

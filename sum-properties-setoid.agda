module sum-properties-setoid where

open import Type
import Level as L
open import Data.Empty using (⊥)
open import Data.Bool.NP
open Data.Bool.NP.Indexed
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
open import Function.Equality using (_⟨$⟩_)

open import sum-setoid

open import Relation.Binary
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_ ; _≗_ ; _≗₂_)

{-
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
-}

Injective : ∀ {a b}{A : Set a}{B : Set b}(f : A → B) → Set (a L.⊔ b)
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

Injectivoid : ∀ {A B : SEToid} → (Setoid.Carrier A → Setoid.Carrier B) → Set
Injectivoid {A}{B} f = ∀ {x y} → Setoid._≈_ B (f x) (f y) → Setoid._≈_ A x y

StableUnderInjection : ∀ {A} → SumPropoid A → Set
StableUnderInjection {A} μ = ∀ p → Setoid._≈_ A =[ p ]⇒ Setoid._≈_ A → Injectivoid {A}{A} p → SumStableUnder μ p

CountStableUnderInjection : ∀ {A} → SumPropoid A → Set
CountStableUnderInjection μ = ∀ p → Injective p → CountStableUnder μ p

{-
#-StableUnderInjection : ∀ {A}{μ : SumPropoid A} → StableUnderInjection μ
    → ∀ f p → Injective p → count μ f ≡ count μ (f ∘ p)
#-StableUnderInjection sui f p p-inj = {!sui p p-inj (toℕ ∘ f)!}
-}

record SearchEq {As Bs : SEToid}(μA : SumPropoid As)(μB : SumPropoid Bs): Set where
  constructor mk
  field
    iso : Inv.Inverse As Bs
  
  private
    A = Setoid.Carrier As
    B = Setoid.Carrier Bs

  from : B → A
  from x = Inv.Inverse.from iso ⟨$⟩ x

  to : A → B
  to x = Inv.Inverse.to iso ⟨$⟩ x

  from-inj : Injectivoid {Bs} {As} from
  from-inj = Inv.Inverse.injective (Inv.sym iso)

  to-inj : Injectivoid {As} {Bs} to
  to-inj = Inv.Inverse.injective iso

  from-pres : ∀ {x y} → Setoid._≈_ Bs x y → Setoid._≈_ As (from x) (from y)
  from-pres {x} {y} x≈y = let open Setoid Bs in to-inj (trans (Inv.Inverse.right-inverse-of iso x) (trans x≈y (sym (Inv.Inverse.right-inverse-of iso y))))

  to-pres : ∀ {x y} → Setoid._≈_ As x y → Setoid._≈_ Bs (to x) (to y)
  to-pres {x} {y} x≈y = let open Setoid As in from-inj (trans (Inv.Inverse.left-inverse-of iso x) (trans x≈y (sym (Inv.Inverse.left-inverse-of iso y))))

  field
    sums-ok : ∀ f → (∀ {x y} → Setoid._≈_ As x y → f x ≡ f y) → sum μA f ≡ sum μB (f ∘ from)

  sums-ok' : ∀ f → (∀ {x y} → Setoid._≈_ Bs x y → f x ≡ f y) → sum μB f ≡ sum μA (f ∘ to)
  sums-ok' f f-pres 
             = sum μB f
             ≡⟨ SumPropoid.search-extoid μB _+_ {f = f}
                  {g = f ∘ to ∘ from} (λ {x}{y} x≈y → f-pres (SB.trans x≈y (SB.sym (Inv.Inverse.right-inverse-of iso y)))) ⟩
               sum μB (f ∘ to ∘ from)
             ≡⟨ ≡.sym (sums-ok (f ∘ to) (λ {x}{y} x≈y → f-pres (from-inj (SA.trans (Inv.Inverse.left-inverse-of iso x) (SA.trans x≈y (SA.sym (Inv.Inverse.left-inverse-of iso y))))))) ⟩
               sum μA (f ∘ to)
             ∎
    where open ≡.≡-Reasoning
          module SB = Setoid Bs
          module SA = Setoid As

  StableUnder≈ : StableUnderInjection μA → StableUnderInjection μB
  StableUnder≈ μA-SUI p p-pres p-inj f f-pres
    = sum μB f
    ≡⟨ sums-ok' f f-pres ⟩
      sum μA (f ∘ to)
    ≡⟨ μA-SUI (from ∘ p ∘ to) (from-pres ∘ p-pres ∘ to-pres) (to-inj ∘ p-inj ∘ from-inj) (f ∘ to) (f-pres ∘ to-pres) ⟩
      sum μA (f ∘ to ∘ from ∘ p ∘ to)
    ≡⟨ ≡.sym (sums-ok' (f ∘ to ∘ from ∘ p) (f-pres ∘ to-pres ∘ from-pres ∘ p-pres)) ⟩
      sum μB (f ∘ to ∘ from ∘ p)
    ≡⟨ search-extoid μB _+_ {f = f ∘ to ∘ from ∘ p} {g = f ∘ p} (f-pres ∘ Setoid.trans Bs (Inv.Inverse.right-inverse-of iso _) ∘ p-pres) ⟩
      sum μB (f ∘ p)
    ∎
    where open ≡.≡-Reasoning

{-
infix 4 _≈_

record _≈_ {A B} (μA : SumProp A)(μB : SumProp B) : Set where
  constructor mk
  field
    iso : A ↔ B
  from : B → A
  from x = Inv.Inverse.from iso ⟨$⟩ x

  to : A → B
  to x = Inv.Inverse.to iso ⟨$⟩ x

  from-inj : Injective from
  from-inj = Inv.Inverse.injective (Inv.sym iso)

  to-inj : Injective to
  to-inj = Inv.Inverse.injective iso

  field
    sums-ok : ∀ f → sum μA f ≡ sum μB (f ∘ from)

  sums-ok' : ∀ f → sum μB f ≡ sum μA (f ∘ to)
  sums-ok' f = sum μB f
             ≡⟨ sum-ext μB (≡.cong f ∘ ≡.sym ∘ Inv.Inverse.right-inverse-of iso) ⟩
               sum μB (f ∘ to ∘ from)
             ≡⟨ ≡.sym (sums-ok (f ∘ to)) ⟩
               sum μA (f ∘ to)
             ∎
    where open ≡.≡-Reasoning

  StableUnder≈ : StableUnderInjection μA → StableUnderInjection μB
  StableUnder≈ μA-SUI p p-inj f
    = sum μB f
    ≡⟨ sums-ok' f ⟩
      sum μA (f ∘ to)
    ≡⟨ μA-SUI (from ∘ p ∘ to) (to-inj ∘ p-inj ∘ from-inj) (f ∘ to)⟩
      sum μA (f ∘ to ∘ from ∘ p ∘ to)
    ≡⟨ ≡.sym (sums-ok' (f ∘ to ∘ from ∘ p)) ⟩
      sum μB (f ∘ to ∘ from ∘ p)
    ≡⟨ sum-ext μB (≡.cong f ∘ Inv.Inverse.right-inverse-of iso ∘ p) ⟩
      sum μB (f ∘ p)
    ∎
    where open ≡.≡-Reasoning


≈-refl : ∀ {A} (μA : SumProp A) → μA ≈ μA
≈-refl μA = mk Inv.id (λ f → ≡.refl)

≈-id : ∀ {A} {μA : SumProp A} → μA ≈ μA
≈-id = ≈-refl _

≈-sym : ∀ {A B}{μA : SumProp A}{μB : SumProp B} → μA ≈ μB → μB ≈ μA
≈-sym A≈B = mk (Inv.sym iso) sums-ok'
  where open _≈_ A≈B

≈-trans : ∀ {A B C}{μA : SumProp A}{μB : SumProp B}{μC : SumProp C} → μA ≈ μB → μB ≈ μC → μA ≈ μC
≈-trans A≈B B≈C = mk (iso B≈C Inv.∘ iso A≈B) (λ f → ≡.trans (sums-ok A≈B f) (sums-ok B≈C (f ∘ from A≈B)))
  where open _≈_

infix 2 _≈∎
infixr 2 _≈⟨_⟩_

_≈∎ : ∀ {A} (μA : SumProp A) → μA ≈ μA
_≈∎ = ≈-refl

_≈⟨_⟩_ : ∀ {A B C} (μA : SumProp A){μB : SumProp B}{μC : SumProp C} → μA ≈ μB → μB ≈ μC → μA ≈ μC
_ ≈⟨ A≈B ⟩ B≈C = ≈-trans A≈B B≈C

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
  iso = Inv.sym Fin∘suc↔⊤⊎Fin

  sums-ok : (_ : _) → _
  sums-ok f = ≡.refl

⊤×A≈A : ∀ {A}{μA : SumProp A} → μ⊤ ×μ μA ≈ μA
⊤×A≈A = mk iso sums-ok where
  iso : _
  iso = ⊤×A↔A

  sums-ok : (_ : _) → _
  sums-ok f = ≡.refl

μFinPres : ∀ {m n} → m ≡ n → μFinSuc m ≈ μFinSuc n
μFinPres eq rewrite eq = ≈-refl _

_+μ-cong_ : ∀ {A B C D}{μA : SumProp A}{μB : SumProp B}{μC : SumProp C}{μD : SumProp D}
          → μA ≈ μC → μB ≈ μD → μA +μ μB ≈ μC +μ μD
A≈C +μ-cong B≈D = mk iso sums-ok where
  open import Relation.Binary.Sum
  iso : _
  iso = (_≈_.iso A≈C) ⊎-cong (_≈_.iso B≈D)

  sums-ok : (_ : _) → _
  sums-ok f = ≡.cong₂ _+_ (_≈_.sums-ok A≈C (f ∘ inj₁)) (_≈_.sums-ok B≈D (f ∘ inj₂))

+μ-assoc : ∀ {A B C}(μA : SumProp A)(μB : SumProp B)(μC : SumProp C)
         → (μA +μ μB) +μ μC ≈ μA +μ (μB +μ μC)
+μ-assoc μA μB μC = mk iso sums-ok where
  iso : _
  iso = ⊎-CMon.assoc _ _ _

  sums-ok : (_ : _) → _
  sums-ok f = ℕ°.+-assoc (sum μA (f ∘ inj₁ ∘ inj₁)) (sum μB (f ∘ inj₁ ∘ inj₂)) (sum μC (f ∘ inj₂))

+μ-comm : ∀ {A B}(μA : SumProp A)(μB : SumProp B)
        → μA +μ μB ≈ μB +μ μA
+μ-comm μA μB = mk iso sums-ok where
  iso : _
  iso = ⊎-CMon.comm _ _

  sums-ok : (_ : _) → _
  sums-ok f = ℕ°.+-comm (sum μA (f ∘ inj₁)) (sum μB (f ∘ inj₂))

_×μ-cong_ :  ∀ {A B C D}{μA : SumProp A}{μB : SumProp B}{μC : SumProp C}{μD : SumProp D}
          → μA ≈ μC → μB ≈ μD → μA ×μ μB ≈ μC ×μ μD
_×μ-cong_ {μA = μA}{μD = μD} A≈C B≈D = mk iso sums-ok where
  open import Relation.Binary.Product.Pointwise
  iso : _
  iso = _≈_.iso A≈C ×-cong _≈_.iso B≈D

  sums-ok : (_ : _) → _
  sums-ok f = ≡.trans (sum-ext μA (_≈_.sums-ok B≈D ∘ curry f))
                      (_≈_.sums-ok A≈C (λ a → sum μD (curry f a ∘ (_≈_.from B≈D))))

×μ-assoc : ∀ {A B C}(μA : SumProp A)(μB : SumProp B)(μC : SumProp C)
         → (μA ×μ μB) ×μ μC ≈ μA ×μ (μB ×μ μC)
×μ-assoc μA μB μC = mk iso sums-ok where
  iso : _
  iso = ×-CMon.assoc _ _ _

  sums-ok : (_ : _) → _
  sums-ok f = ≡.refl

×μ-comm : ∀ {A B}(μA : SumProp A)(μB : SumProp B)
        → μA ×μ μB ≈ μB ×μ μA
×μ-comm μA μB = mk iso sums-ok where
  iso : _
  iso = ×-CMon.comm _ _

  sums-ok : (_ : _) → _
  sums-ok f = sum-swap μA μB (curry f)

×+-distrib : ∀ {A B C}(μA : SumProp A)(μB : SumProp B)(μC : SumProp C)
           → (μA +μ μB) ×μ μC ≈ (μA ×μ μC) +μ (μB ×μ μC)
×+-distrib μA μB μC = mk iso sums-ok where
  iso : _
  iso = ×⊎°.distribʳ _ _ _

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

Finable : ∀ {A} → SumProp A → Set
Finable μA = Σ ℕ λ FinCard → μA ≈ μFinSuc FinCard

⊤-Finable : Finable μ⊤
⊤-Finable = 0 , ≈-sym Fin0≈⊤

Fin-Finable : ∀ {n} → Finable (μFinSuc n)
Fin-Finable {n} = n , ≈-refl (μFinSuc n)

+-Finable : ∀ {A B}(μA : SumProp A)(μB : SumProp B) → Finable μA → Finable μB → Finable (μA +μ μB)
+-Finable μA μB (|A| , A≈) (|B| , B≈) = (|A| + suc |B|) ,
  ( μA +μ μB
  ≈⟨ A≈ +μ-cong B≈ ⟩
    μFinSuc |A| +μ μFinSuc |B|
  ≈⟨ +-≈ |A| |B| ⟩
    μFinSuc (|A| + suc |B|) ≈∎)

×-Finable : ∀ {A B}(μA : SumProp A)(μB : SumProp B) → Finable μA → Finable μB → Finable (μA ×μ μB)
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
  μFinSUI {n} p p-inj f rewrite ≡.sym (sumFin-spec n f)
                              | ≡.sym (sumFin-spec n (f ∘ p))
                              = sumFinSUI (suc n) f p p-inj

StableIfFinable : ∀ {A} (μA : SumProp A) → Finable μA → StableUnderInjection μA
StableIfFinable μA (_ , A≈Fin)
  = _≈_.StableUnder≈ (≈-sym A≈Fin) μFinSUI

-- -}

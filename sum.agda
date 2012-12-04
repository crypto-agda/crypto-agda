import Level as L
open import Type
open import Function
open import Algebra
open import Algebra.FunctionProperties.NP
open import Data.Nat.NP hiding (_^_)
open import Data.Nat.Properties
open import Data.Unit hiding (_≤_)
open import Data.Sum
open import Data.Maybe.NP
open import Data.Product
open import Data.Bits
open import Data.Bool.NP as Bool
open import Function.Equality using (_⟨$⟩_)
import Function.Inverse as FI
open FI using (_↔_; module Inverse)
import Function.Related as FR
open import Function.Related.TypeIsomorphisms.NP
open import Relation.Binary.NP
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; _≗_)

module sum where

_≤°_ : ∀ {A : ★}(f g : A → ℕ) → ★
f ≤° g = ∀ x → f x ≤ g x

Semigroup₀ = Semigroup L.zero L.zero
Monoid₀ = Monoid L.zero L.zero
CommutativeMonoid₀ = CommutativeMonoid L.zero L.zero

module SgrpExtra (sg : Semigroup₀) where
  open Semigroup sg
  open Setoid-Reasoning (Semigroup.setoid sg) public
  C : ★
  C = Carrier
  _≈°_ : ∀ {A : ★} (f g : A → C) → ★
  f ≈° g = ∀ x → f x ≈ g x
  _∙°_   : ∀ {A : ★} (f g : A → C) → A → C
  (f ∙° g) x = f x ∙ g x
  infixl 7 _-∙-_
  _-∙-_ : _∙_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  _-∙-_ = ∙-cong

module Sgrp (sg : Semigroup₀) where
  open Semigroup sg public
  open SgrpExtra sg public

module Mon (m : Monoid₀) where
  open Monoid m public
  sg = semigroup
  open SgrpExtra semigroup public

module CMon (cm : CommutativeMonoid₀) where
  open CommutativeMonoid cm public
  sg = semigroup
  m = monoid
  open SgrpExtra sg public

  ∙-interchange : Interchange _≈_ _∙_ _∙_
  ∙-interchange = InterchangeFromAssocCommCong.∙-interchange
                    _≈_ isEquivalence
                    _∙_ assoc comm (λ _ → flip ∙-cong refl)

Search : ★ → ★₁
Search A = ∀ {B} → (_∙_ : B → B → B) → (A → B) → B
-- Search A = ∀ {I : ★} {F : I → ★} → (_∙_ : ∀ {i} → F i → F i → F i) → ∀ {i} → (A → F i) → F i

SearchMon : ★ → ★₁
SearchMon A = (m : Monoid₀) → let open Mon m in
                              (A → C) → C

searchMonFromSearch : ∀ {A} → Search A → SearchMon A
searchMonFromSearch s m = s _∙_ where open Mon m

Sum : ★ → ★
Sum A = (A → ℕ) → ℕ

Count : ★ → ★
Count A = (A → Bit) → ℕ

SearchInd : ∀ {A} → Search A → ★₁
SearchInd {A} srch = ∀ (P  : Search A → ★)
                       (P∙ : ∀ {s₀ s₁ : Search A} → P s₀ → P s₁ → P (λ _∙_ f → s₀ _∙_ f ∙ s₁ _∙_ f))
                       (Pf : ∀ x → P (λ _ f → f x))
                     →  P srch

SearchMono : ∀ {A} → Search A → ★₁
SearchMono sᴬ = ∀ {C} (_⊆_ : C → C → ★) →
                ∀ {_∙_} (∙-mono : _∙_ Preserves₂ _⊆_ ⟶ _⊆_ ⟶ _⊆_)
                  {f g} →
                  (∀ x → f x ⊆ g x) → sᴬ _∙_ f ⊆ sᴬ _∙_ g

SearchSgExt : ∀ {A} → Search A → ★₁
SearchSgExt sᴬ = ∀ sg {f g} → let open Sgrp sg in
                              f ≈° g → sᴬ _∙_ f ≈ sᴬ _∙_ g

SearchExt : ∀ {A} → Search A → ★₁
SearchExt {A} sᴬ = ∀ {B} op {f g : A → B} → f ≗ g → sᴬ op f ≡ sᴬ op g

SumExt : ∀ {A} → Sum A → ★
SumExt sumᴬ = ∀ {f g} → f ≗ g → sumᴬ f ≡ sumᴬ g

CountExt : ∀ {A} → Count A → ★
CountExt countᴬ = ∀ {f g} → f ≗ g → countᴬ f ≡ countᴬ g

Searchε : ∀ {A} → SearchMon A → ★₁
Searchε sᴬ = ∀ m → let open Mon m in
                   sᴬ m (const ε) ≈ ε

SumZero : ∀ {A} → Sum A → ★
SumZero sumᴬ = sumᴬ (λ _ → 0) ≡ 0

SumLin : ∀ {A} → Sum A → ★
SumLin sumᴬ = ∀ f k → sumᴬ (λ x → k * f x) ≡ k * sumᴬ f

SearchHom : ∀ {A} → Search A → ★₁
SearchHom sᴬ = ∀ sg f g → let open Sgrp sg in
                          sᴬ _∙_ (f ∙° g) ≈ sᴬ _∙_ f ∙ sᴬ _∙_ g

SearchMonHom : ∀ {A} → SearchMon A → ★₁
SearchMonHom sᴬ = ∀ (cm : CommutativeMonoid₀) f g →
                         let open CMon cm in
                         sᴬ m (f ∙° g) ≈ sᴬ m f ∙ sᴬ m g

SumHom : ∀ {A} → Sum A → ★
SumHom sumᴬ = ∀ f g → sumᴬ (λ x → f x + g x) ≡ sumᴬ f + sumᴬ g

SumMono : ∀ {A} → Sum A → ★
SumMono sumᴬ = ∀ {f g} → f ≤° g → sumᴬ f ≤ sumᴬ g

SearchSwap : ∀ {A} → Search A → ★₁
SearchSwap {A} sᴬ = ∀ {B} sg f →
                    let open Sgrp sg in ∀ {sᴮ : (B → C) → C}
                  → (hom : ∀ f g → sᴮ (f ∙° g) ≈ sᴮ f ∙ sᴮ g)
                  → sᴬ _∙_ (sᴮ ∘ f) ≈ sᴮ (sᴬ _∙_ ∘ flip f)

sum-lin⇒sum-zero : ∀ {A} → {sum : Sum A} → SumLin sum → SumZero sum
sum-lin⇒sum-zero sum-lin = sum-lin (λ _ → 0) 0

sum-mono⇒sum-ext : ∀ {A} → {sum : Sum A} → SumMono sum → SumExt sum
sum-mono⇒sum-ext sum-mono f≗g = ℕ≤.antisym (sum-mono (ℕ≤.reflexive ∘ f≗g)) (sum-mono (ℕ≤.reflexive ∘ ≡.sym ∘ f≗g))

sum-ext+sum-hom⇒sum-mono : ∀ {A} → {sum : Sum A} → SumExt sum → SumHom sum → SumMono sum
sum-ext+sum-hom⇒sum-mono {sum = sum} sum-ext sum-hom {f} {g} f≤°g =
    sum f                         ≤⟨ m≤m+n _ _ ⟩
    sum f + sum (λ x → g x ∸ f x) ≡⟨ ≡.sym (sum-hom _ _) ⟩
    sum (λ x → f x + (g x ∸ f x)) ≡⟨ sum-ext (m+n∸m≡n ∘ f≤°g) ⟩
    sum g ∎ where open ≤-Reasoning

record SumProp A : ★₁ where
  constructor _,_
  field
    search     : Search A
    search-ind : SearchInd search

  search-sg-ext : SearchSgExt search
  search-sg-ext sg {f} {g} f≈°g = search-ind (λ s → s _ f ≈ s _ g) ∙-cong f≈°g
    where open Sgrp sg

  search-ext : SearchExt search
  search-ext op = search-ind (λ s → s _ _ ≡ s _ _) (≡.cong₂ op)

  search-mono : SearchMono search
  search-mono _⊆_ _∙-mono_ {f} {g} f⊆°g = search-ind (λ s → s _ f ⊆ s _ g) _∙-mono_ f⊆°g

  search-swap : SearchSwap search
  search-swap sg f {sᴮ} pf = search-ind (λ s → s _ (sᴮ ∘ f) ≈ sᴮ (s _ ∘ flip f)) (λ p q → trans (∙-cong p q) (sym (pf _ _))) (λ _ → refl)
    where open Sgrp sg

  searchMon : SearchMon A
  searchMon m = search _∙_
    where open Mon m

  search-ε : Searchε searchMon
  search-ε m = search-ind (λ s → s _ (const ε) ≈ ε) (λ x≈ε y≈ε → trans (∙-cong x≈ε y≈ε) (proj₁ identity ε)) (λ _ → refl)
    where open Mon m

  search-hom : SearchMonHom searchMon
  search-hom cm f g = search-ind (λ s → s _ (f ∙° g) ≈ s _ f ∙ s _ g)
                                 (λ p₀ p₁ → trans (∙-cong p₀ p₁) (∙-interchange _ _ _ _)) (λ _ → refl)
    where open CMon cm

  search-hom′ :
      ∀ {S T}
        (_+_ : Op₂ S)
        (_*_ : Op₂ T)
        (f   : S → T)
        (g   : A → S)
        (hom : ∀ x y → f (x + y) ≡ f x * f y)
        → f (search _+_ g) ≡ search _*_ (f ∘ g)
  search-hom′ _+_ _*_ f g hom = search-ind (λ s → f (s _+_ g) ≡ s _*_ (f ∘ g))
                                           (λ p q → ≡.trans (hom _ _) (≡.cong₂ _*_ p q))
                                           (λ _ → ≡.refl)

  sum : Sum A
  sum = search _+_

  sum-ext : SumExt sum
  sum-ext = search-ext _+_

  sum-zero : SumZero sum
  sum-zero = search-ε ℕ+.monoid

  sum-hom : SumHom sum
  sum-hom = search-hom ℕ°.+-commutativeMonoid

  sum-mono : SumMono sum
  sum-mono = search-mono _≤_ _+-mono_

  sum-lin : SumLin sum
  sum-lin f zero    = sum-zero
  sum-lin f (suc k) = ≡.trans (sum-hom f (λ x → k * f x)) (≡.cong₂ _+_ (≡.refl {x = sum f}) (sum-lin f k))

  Card : ℕ
  Card = sum (const 1)

  count : Count A
  count f = sum (Bool.toℕ ∘ f)

  count-ext : CountExt count
  count-ext f≗g = sum-ext (≡.cong Bool.toℕ ∘ f≗g)

open SumProp public

search-swap' : ∀ {A B} cm (μA : SumProp A) (μB : SumProp B) f →
               let open CMon cm
                   sᴬ = search μA _∙_
                   sᴮ = search μB _∙_ in
               sᴬ (sᴮ ∘ f) ≈ sᴮ (sᴬ ∘ flip f)
search-swap' cm μA μB f = search-swap μA sg f (search-hom μB cm)
  where open CMon cm

sum-swap : ∀ {A B} (μA : SumProp A) (μB : SumProp B) f →
           sum μA (sum μB ∘ f) ≡ sum μB (sum μA ∘ flip f)
sum-swap = search-swap' ℕ°.+-commutativeMonoid

_≈Sum_ : ∀ {A} → (sum₀ sum₁ : Sum A) → ★
sum₀ ≈Sum sum₁ = ∀ f → sum₀ f ≡ sum₁ f

_≈Search_ : ∀ {A} → (s₀ s₁ : Search A) → ★₁
s₀ ≈Search s₁ = ∀ {B} (op : Op₂ B) f → s₀ op f ≡ s₁ op f

μ⊤ : SumProp ⊤
μ⊤ = srch , ind
  where
    srch : Search ⊤
    srch _ f = f _

    ind : SearchInd srch
    ind _ _ Pf = Pf _

μBit : SumProp Bit
μBit = searchBit , ind
  where
    searchBit : Search Bit
    searchBit _∙_ f = f 0b ∙ f 1b

    ind : SearchInd searchBit
    ind _ _P∙_ Pf = Pf 0b P∙ Pf 1b

infixr 4 _+Search_

_+Search_ : ∀ {A B} → Search A → Search B → Search (A ⊎ B)
(searchᴬ +Search searchᴮ) _∙_ f = searchᴬ _∙_ (f ∘ inj₁) ∙ searchᴮ _∙_ (f ∘ inj₂)

_+SearchInd_ : ∀ {A B} {sᴬ : Search A} {sᴮ : Search B} →
                 SearchInd sᴬ → SearchInd sᴮ → SearchInd (sᴬ +Search sᴮ)
(Psᴬ +SearchInd Psᴮ) P P∙ Pf
  = P∙ (Psᴬ (λ s → P (λ _ f → s _ (f ∘ inj₁))) P∙ (Pf ∘ inj₁))
       (Psᴮ (λ s → P (λ _ f → s _ (f ∘ inj₂))) P∙ (Pf ∘ inj₂))

infixr 4 _+Sum_

_+Sum_ : ∀ {A B} → Sum A → Sum B → Sum (A ⊎ B)
(sumᴬ +Sum sumᴮ) f = sumᴬ (f ∘ inj₁) + sumᴮ (f ∘ inj₂)

_+μ_ : ∀ {A B} → SumProp A → SumProp B → SumProp (A ⊎ B)
μA +μ μB = _ , search-ind μA +SearchInd search-ind μB

infixr 4 _×Search_

-- liftM2 _,_ in the continuation monad
_×Search_ : ∀ {A B} → Search A → Search B → Search (A × B)
(searchᴬ ×Search searchᴮ) op f = searchᴬ op (λ x → searchᴮ op (curry f x))

_×SearchInd_ : ∀ {A B} {sᴬ : Search A} {sᴮ : Search B}
               → SearchInd sᴬ → SearchInd sᴮ → SearchInd (sᴬ ×Search sᴮ)
(Psᴬ ×SearchInd Psᴮ) P P∙ Pf =
  Psᴬ (λ s → P (λ _ _ → s _ _)) P∙ (Psᴮ (λ s → P (λ _ _ → s _ _)) P∙ ∘ curry Pf)

_×SearchExt_ : ∀ {A B} {sᴬ : Search A} {sᴮ : Search B} →
              SearchExt sᴬ → SearchExt sᴮ → SearchExt (sᴬ ×Search sᴮ)
(sᴬ-ext ×SearchExt sᴮ-ext) sg f≗g = sᴬ-ext sg (sᴮ-ext sg ∘ curry f≗g)

infixr 4 _×Sum_

-- liftM2 _,_ in the continuation monad
_×Sum_ : ∀ {A B} → Sum A → Sum B → Sum (A × B)
(sumᴬ ×Sum sumᴮ) f = sumᴬ (λ x₀ →
                       sumᴮ (λ x₁ →
                         f (x₀ , x₁)))

infixr 4 _×μ_

_×μ_ : ∀ {A B} → SumProp A → SumProp B → SumProp (A × B)
μA ×μ μB = _ , search-ind μA ×SearchInd search-ind μB

sum-const : ∀ {A} (μA : SumProp A) → ∀ k → sum μA (const k) ≡ Card μA * k
sum-const μA k
  rewrite ℕ°.*-comm (Card μA) k
        | ≡.sym (sum-lin μA (const 1) k)
        | proj₂ ℕ°.*-identity k = ≡.refl

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
        | sumf≡sumg = ≡.refl

_×Sum-proj₂'_ : ∀ {A B}
                  (μA : SumProp A) (μB : SumProp B)
                  {f} {g} →
                  sum μB f ≡ sum μB g →
                  sum (μA ×μ μB) (f ∘ proj₂) ≡ sum (μA ×μ μB) (g ∘ proj₂)
(μA ×Sum-proj₂' μB) sumf≡sumg = sum-ext μA (const sumf≡sumg)

μ-view : ∀ {A B} → (A → B) → SumProp A → SumProp B
μ-view {A}{B} A→B μA = searchᴮ , ind
  where
    searchᴮ : Search B
    searchᴮ m f = search μA m (f ∘ A→B)

    ind : SearchInd searchᴮ
    ind P P∙ Pf = search-ind μA (λ s → P (λ _ f → s _ (f ∘ A→B))) P∙ (Pf ∘ A→B)

μ-iso : ∀ {A B} → (A ↔ B) → SumProp A → SumProp B
μ-iso A↔B = μ-view (_⟨$⟩_ (Inverse.to A↔B))

μ-view-preserve : ∀ {A B} (A→B : A → B)(B→A : B → A)(A≈B : id ≗ B→A ∘ A→B) f (μA : SumProp A) → sum μA f ≡ sum (μ-view A→B μA) (f ∘ B→A)
μ-view-preserve A→B B→A A≈B f μA = sum-ext μA (≡.cong f ∘ A≈B)

μ-iso-preserve : ∀ {A B} (A↔B : A ↔ B) f (μA : SumProp A) → sum μA f ≡ sum (μ-iso A↔B μA) (f ∘ _⟨$⟩_ (Inverse.from A↔B))
μ-iso-preserve A↔B f μA = μ-view-preserve (_⟨$⟩_ (Inverse.to A↔B)) (_⟨$⟩_ (Inverse.from A↔B))
                            (≡.sym ∘ Inverse.left-inverse-of A↔B) f μA

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec.NP as Vec using (Vec; tabulate; _++_) renaming (map to vmap; sum to vsum; foldr to vfoldr; foldr₁ to vfoldr₁)

vmsum : ∀ m {n} → let open Mon m in
                  Vec C n → C
vmsum m = vfoldr _ _∙_ ε
  where open Monoid m

vsgsum : ∀ sg {n} → let open Sgrp sg in
                    Vec C (suc n) → C
vsgsum sg = vfoldr₁ _∙_
  where open Sgrp sg

-- let's recall that: tabulate f ≗ vmap f (allFin n)

-- searchMonFin : ∀ n → SearchMon (Fin n)
-- searchMonFin n m f = vmsum m (tabulate f)

searchFinSuc : ∀ n → Search (Fin (suc n))
searchFinSuc n _∙_ f = vfoldr₁ _∙_ (tabulate f)

μMaybe : ∀ {A} → SumProp A → SumProp (Maybe A)
μMaybe μA = μ-iso (FI.sym Maybe↔⊤⊎) (μ⊤ +μ μA)

μMaybe^ : ∀ {A} n → SumProp A → SumProp (Maybe^ n A)
μMaybe^ zero    μA = μA
μMaybe^ (suc n) μA = μMaybe (μMaybe^ n μA)

{-
μFin : ∀ n → SumProp (Fin (suc n))
μFin n = searchFinSuc n , ind n
  where ind : ∀ n → SearchInd (searchFinSuc n)
        ind zero    P P∙ Pf = Pf zero
        ind (suc n) P P∙ Pf = P∙ (Pf zero) (ind n (λ s → P (λ op f → s op (f ∘ suc))) P∙ (Pf ∘ suc))
-}

μFin : ∀ n → SumProp (Fin (suc n))
μFin n = μ-iso (Maybe^⊤↔Fin1+ n) (μMaybe^ n μ⊤)

sumFin : ∀ n → Sum (Fin n)
sumFin n f = vsum (tabulate f)

sumFin-spec : ∀ n → sumFin (suc n) ≗ sum (μFin n)
sumFin-spec zero    f = ℕ°.+-comm (f zero) 0
sumFin-spec (suc n) f = ≡.cong (_+_ (f zero)) (sumFin-spec n (f ∘ suc))

μ^ : ∀ {A} (μA : SumProp A) n → SumProp (A ^ n)
μ^ μA zero    = μ⊤
μ^ μA (suc n) = μA ×μ μ^ μA n

μVec : ∀ {A} (μA : SumProp A) n  → SumProp (Vec A n)
μVec μA n = μ-iso (^↔Vec n) (μ^ μA n)

searchVec : ∀ {A} n → Search A → Search (Vec A n)
searchVec zero    searchᴬ op f = f []
searchVec (suc n) searchᴬ op f = searchᴬ op (λ x → searchVec n searchᴬ op (f ∘ _∷_ x))

searchVec-spec : ∀ {A} (μA : SumProp A) n → searchVec n (search μA) ≈Search search (μVec μA n)
searchVec-spec μA zero    op f = ≡.refl
searchVec-spec μA (suc n) op f = search-ext μA op (λ x → searchVec-spec μA n op (f ∘ _∷_ x))

searchVec-++ : ∀ {A} n {m} (μA : SumProp A) sg
               → let open Sgrp sg in
                 (f : Vec A (n + m) → C)
               → search (μVec μA (n + m)) _∙_ f
               ≈ search (μVec μA n) _∙_ (λ xs →
                   search (μVec μA m) _∙_ (λ ys →
                     f (xs ++ ys)))
searchVec-++ zero    μA sg f = Sgrp.refl sg
searchVec-++ (suc n) μA sg f = search-sg-ext μA sg (λ x →
                                 searchVec-++ n μA sg (f ∘ _∷_ x))

sumVec-swap : ∀ {A} n {m} (μA : SumProp A)(f : Vec A (n + m) → ℕ)
            → sum (μVec μA n) (λ xs → sum (μVec μA m) (λ ys → f (xs ++ ys)))
            ≡ sum (μVec μA m) (λ ys → sum (μVec μA n) (λ xs → f (xs ++ ys)))
sumVec-swap n {m} μA f = sum-swap (μVec μA n) (μVec μA m) (λ xs ys → f (xs ++ ys))

swapS : ∀ {A B} → SumProp (A × B) → SumProp (B × A)
swapS = μ-iso swap-iso

swapS-preserve : ∀ {A B} f (μA×B : SumProp (A × B)) → sum μA×B f ≡ sum (swapS μA×B) (f ∘ swap)
swapS-preserve = μ-iso-preserve swap-iso
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

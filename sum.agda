import Level as L
open import Type
open import Function
open import Algebra
open import Algebra.FunctionProperties.NP
open import Data.Nat.NP
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
Preorder₀ = Preorder L.zero L.zero L.zero

module PO (po : Preorder₀) where
  open Preorder po public renaming (_∼_ to _⊆_)
  _⊆°_ : ∀ {A : ★}(f g : A → Carrier) → ★
  f ⊆° g = ∀ x → f x ⊆ g x

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
  Is-ε : Carrier → ★
  Is-ε x = x ≈ ε

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
SearchInd {A} srch = ∀ {C}
                       (P   : ((A → C) → C) → ★)
                       {_∙_ : Op₂ C}
                       (P∙  : ∀ {s₀ s₁} → P s₀ → P s₁ → P (λ f → s₀ f ∙ s₁ f))
                       (Pf  : ∀ x → P (λ f → f x))
                     → P (srch _∙_)

SearchInd' : ∀ {A} → Search A → ★₁
SearchInd' {A} srch = ∀ {C}
                        (P   : C → ★)
                        {_∙_ : C → C → C}
                        (P∙  : ∀ {x y} → P x → P y → P (x ∙ y))
                        {f   : A → C}
                        (Pf  : ∀ x → P (f x))
                      → P (srch _∙_ f)

SearchMono : ∀ {A} → Search A → ★₁
SearchMono sᴬ = ∀ {C : ★} (_⊆_ : C → C → ★) → -- let open PO {C} _⊆_ in
                ∀ {_∙_} (∙-mono : _∙_ Preserves₂ _⊆_ ⟶ _⊆_ ⟶ _⊆_)
                  {f g} →
                  (∀ x → f x ⊆ g x) → sᴬ _∙_ f ⊆ sᴬ _∙_ g

SearchExt : ∀ {A} → Search A → ★₁
SearchExt sᴬ = ∀ sg {f g} → let open Sgrp sg in
                            f ≈° g → sᴬ _∙_ f ≈ sᴬ _∙_ g

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

{-search-hom′ :
  ∀ {a b}
    {A : Set a} {B : Set b} {R}
    (_+_ : A → A → A)
    (_*_ : B → B → B)
    (f : A → B)
    (p : R → A)
    (hom : ∀ x y → f (x + y) ≡ f x * f y)
    → f (search _+_ p) ≡ search _*_ (f ∘ p)
search-hom′ = ?
{-
search-hom {zero}  _   _   _ _ _   = refl
search-hom {suc n} _+_ _*_ f p hom =
   trans (hom _ _)
         (cong₂ _*_ (search-hom _+_ _*_ f (p ∘ 0∷_) hom)
                    (search-hom _+_ _*_ f (p ∘ 1∷_) hom))
-}
-}

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
  constructor mk
  field
    search      : Search A
    search-ind  : SearchInd search

  search-ind' : SearchInd' search
  search-ind' P P∙ {f} Pf = search-ind (λ s → P (s f)) P∙ Pf

  search-ext : SearchExt search
  search-ext sg {f} {g} f≈°g = search-ind (λ s → s f ≈ s g) ∙-cong f≈°g
    where open Sgrp sg

  search-mono : SearchMono search
  search-mono _⊆_ {_∙_} _∙-mono_ {f} {g} f⊆°g = search-ind (λ s → s f ⊆ s g) _∙-mono_ f⊆°g

  search-swap : SearchSwap search
  search-swap sg f {sᴮ} pf = search-ind (λ s → s (sᴮ ∘ f) ≈ sᴮ (s ∘ flip f)) (λ p q → trans (∙-cong p q) (sym (pf _ _))) (λ _ → refl)
    where open Sgrp sg

  searchMon : SearchMon A
  searchMon m = search _∙_
    where open Mon m

  search-ε : Searchε searchMon
  search-ε m = search-ind' Is-ε (λ x≈ε y≈ε → trans (∙-cong x≈ε y≈ε) (proj₁ identity ε)) (λ _ → refl)
    where open Mon m

  search-hom : SearchMonHom searchMon
  search-hom cm f g = search-ind (λ s → s (f ∙° g) ≈ s f ∙ s g)
                                 (λ p₀ p₁ → trans (∙-cong p₀ p₁) (∙-interchange _ _ _ _)) (λ _ → refl)
    where open CMon cm

  sum : Sum A
  sum = search _+_

  sum-ext : SumExt sum
  sum-ext = search-ext ℕ+.semigroup

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

μ⊤ : SumProp ⊤
μ⊤ = mk search⊤ ind
  where
    search⊤ : Search ⊤
    search⊤ _ f = f _

    ind : SearchInd search⊤
    ind _ _ Pf = Pf _

    {- derived from ind
    ext : SearchExt search⊤
    ext _ f≗g = f≗g _

    searchMon⊤ : SearchMon ⊤
    searchMon⊤ _ f = f _

    mono : SearchMono search⊤
    mono _ _ f≤°g = f≤°g _

    eps : Searchε searchMon⊤
    eps m = Monoid.refl m

    search⊤-swap : SearchSwap search⊤
    search⊤-swap sg f hom = refl
      where open Sgrp sg

    hom : SearchMonHom searchMon⊤
    hom m f g = CommutativeMonoid.refl m
    -}

μBit : SumProp Bit
μBit = mk searchBit ind
  where
    searchBit : Search Bit
    searchBit _∙_ f = f 0b ∙ f 1b

    ind : SearchInd searchBit
    ind _ _P∙_ Pf = Pf 0b P∙ Pf 1b

    {- derived from ind
    searchMonBit : SearchMon Bit
    searchMonBit m f = f 0b ∙ f 1b
      where open Mon m

    ext : SearchExt searchBit
    ext sg f≗g = f≗g 0b -∙- f≗g 1b
      where open Sgrp sg

    mono : SearchMono searchBit
    mono po _∙-mono_ f⊆°g = f⊆°g 0b ∙-mono f⊆°g 1b

    eps : Searchε searchMonBit
    eps m = proj₁ identity ε
      where open Monoid m

    hom : SearchMonHom searchMonBit
    hom cm f g = ∙-interchange (f 0b) (g 0b) (f 1b) (g 1b)
      where open CMon cm

    sumBit : Sum Bit
    sumBit f = f 0b + f 1b

    swp : SearchSwap searchBit
    swp sg f homᴮ = sym (homᴮ (f 0b) (f 1b))
      where open Sgrp sg
    -}

infixr 4 _+Search_

_+Search_ : ∀ {A B} → Search A → Search B → Search (A ⊎ B)
(searchᴬ +Search searchᴮ) _∙_ f = searchᴬ _∙_ (f ∘ inj₁) ∙ searchᴮ _∙_ (f ∘ inj₂)

_+SearchInd'_ : ∀ {A B} {sᴬ : Search A} {sᴮ : Search B} →
                       SearchInd' sᴬ → SearchInd' sᴮ → SearchInd' (sᴬ +Search sᴮ)
(Psᴬ +SearchInd' Psᴮ) P P∙ Pf = P∙ (Psᴬ P P∙ (Pf ∘ inj₁)) (Psᴮ P P∙ (Pf ∘ inj₂))

_+SearchInd_ : ∀ {A B} {sᴬ : Search A} {sᴮ : Search B} →
                       SearchInd sᴬ → SearchInd sᴮ → SearchInd (sᴬ +Search sᴮ)
(Psᴬ +SearchInd Psᴮ) P P∙ Pf
  = P∙ (Psᴬ (λ s → P (λ f → s (f ∘ inj₁))) P∙ (Pf ∘ inj₁))
       (Psᴮ (λ s → P (λ f → s (f ∘ inj₂))) P∙ (Pf ∘ inj₂))

infixr 4 _+Sum_

_+Sum_ : ∀ {A B} → Sum A → Sum B → Sum (A ⊎ B)
(sumᴬ +Sum sumᴮ) f = sumᴬ (f ∘ inj₁) + sumᴮ (f ∘ inj₂)

_+μ_ : ∀ {A B} → SumProp A
               → SumProp B
               → SumProp (A ⊎ B)
_+μ_ {A} {B} μA μB = mk _ (search-ind μA +SearchInd search-ind μB)
    {- derived from ind
  where
    ext : SearchExt srch
    ext sg f≗g = search-ext μA sg (f≗g ∘ inj₁) -∙- search-ext μB sg (f≗g ∘ inj₂)
      where open Sgrp sg

    sᴬ : Search A
    sᴬ = search μA
    sᴮ : Search B
    sᴮ = search μB
    srch : Search (A ⊎ B)
    srch = sᴬ +Search sᴮ
    sMonᴬ = searchMon μA
    sMonᴮ = searchMon μB
    srchMon = searchMonFromSearch srch
    eps : Searchε srchMon
    eps m = srchMon m (const ε)
          ≈⟨ search-ε μA m -∙- search-ε μB m ⟩
            ε ∙ ε
          ≈⟨ proj₁ identity ε ⟩
            ε
          ∎
      where open Mon m

    mono : SearchMono srch
    mono po _∙-mono_ f⊆°g = monoᴬ (f⊆°g ∘ inj₁) ∙-mono monoᴮ (f⊆°g ∘ inj₂)
      where
      monoᴬ = search-mono μA po _∙-mono_
      monoᴮ = search-mono μB po _∙-mono_

    hom : SearchMonHom srchMon
    hom cm f g
      = srchMon m (f ∙° g)
      ≈⟨ search-hom μA cm (f ∘ inj₁) (g ∘ inj₁) -∙-
         search-hom μB cm (f ∘ inj₂) (g ∘ inj₂) ⟩
        (sMonᴬ m (f ∘ inj₁) ∙ sMonᴬ m (g ∘ inj₁)) ∙
        (sMonᴮ m (f ∘ inj₂) ∙ sMonᴮ m (g ∘ inj₂))
      ≈⟨ ∙-interchange (sMonᴬ m (f ∘ inj₁)) (sMonᴬ m (g ∘ inj₁))
                       (sMonᴮ m (f ∘ inj₂)) (sMonᴮ m (g ∘ inj₂)) ⟩
        srchMon m f ∙ srchMon m g
      ∎
      where open CMon cm

    swp : SearchSwap srch
    swp sg f hom = trans (∙-cong (search-swap μA sg (f ∘ inj₁) hom) (search-swap μB sg (f ∘ inj₂) hom)) (sym (hom g h))
      where open Sgrp sg
            g = λ x → search μA _∙_ (λ y → f (inj₁ y) x)
            h = λ x → search μB _∙_ (λ y → f (inj₂ y) x)
    -}

infixr 4 _×Search_

-- liftM2 _,_ in the continuation monad
_×Search_ : ∀ {A B} → Search A → Search B → Search (A × B)
(searchᴬ ×Search searchᴮ) m f = searchᴬ m (λ x₀ →
                                  searchᴮ m (λ x₁ →
                                    f (x₀ , x₁)))

_×SearchInd'_ : ∀ {A B} {sᴬ : Search A} {sᴮ : Search B}
                       (Psᴬ : SearchInd' sᴬ)
                       (Psᴮ : SearchInd' sᴮ) → SearchInd' (sᴬ ×Search sᴮ)
(Psᴬ ×SearchInd' Psᴮ) P P∙ Pf = Psᴬ P P∙ (λ x → Psᴮ P P∙ (curry Pf x))

_×SearchInd_ : ∀ {A B} {sᴬ : Search A} {sᴮ : Search B}
                       (Psᴬ : SearchInd sᴬ)
                       (Psᴮ : SearchInd sᴮ) → SearchInd (sᴬ ×Search sᴮ)
_×SearchInd_ {sᴬ = sᴬ} {sᴮ} Psᴬ Psᴮ P {_∙_} P∙ Pf =
  Psᴬ (λ s → P (λ f → s (λ x → sᴮ _∙_ (curry f x)))) P∙ (λ x → Psᴮ (λ s → P (λ f → s (curry f x))) P∙ (curry Pf x))

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

_×μ_ : ∀ {A B} → SumProp A
               → SumProp B
               → SumProp (A × B)
(μA ×μ μB) = mk _ (search-ind μA ×SearchInd search-ind μB)
{- derived from SearchInd
   where
     srch = search μA ×Search search μB
     srchMon = searchMonFromSearch srch

     ext : SearchExt srch
     ext sg f≗g = search-ext μA sg (search-ext μB sg ∘ curry f≗g)

     eps : Searchε srchMon
     eps m = srchMon m (const ε)
           ≈⟨ search-ext μA sg (const (search-ε μB m)) ⟩
             searchMon μA m (const ε)
           ≈⟨ search-ε μA m ⟩
             ε
           ∎
       where open Mon m

     mono : SearchMono srch
     mono po ∙mono f≤°g = monoᴬ (monoᴮ ∘ curry f≤°g)
      where
      monoᴬ = search-mono μA po ∙mono
      monoᴮ = search-mono μB po ∙mono

     hom : SearchMonHom srchMon
     hom cm f g
       = srch _∙_ (f ∙° g)
       ≈⟨ search-ext μA sg (λ x → search-hom μB cm (curry f x) (curry g x)) ⟩
         search μA _∙_ (λ x → search μB _∙_ (curry f x) ∙ search μB _∙_ (curry g x))
       ≈⟨ search-hom μA cm (search μB _∙_ ∘ curry f) (search μB _∙_ ∘ curry g) ⟩
         srch _∙_ f ∙ srch _∙_ g
       ∎ where open CMon cm

     swp : SearchSwap srch
     swp sg f {g} hom = sᴬᴮ (g ∘ f)
                      ≈⟨ search-ext μA sg (λ x → search-swap μB sg (curry f x) hom) ⟩
                        sᴬ (λ z → g (λ x → sᴮ (curry (flip f x) z)))
                      ≈⟨ search-swap μA sg (λ z x → sᴮ (curry (flip f x) z)) hom ⟩
                        g (sᴬᴮ ∘ flip f)
                      ∎
       where open Sgrp sg
             sᴬ = search μA _∙_
             sᴮ = search μB _∙_
             sᴬᴮ = srch _∙_
             -}

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
μ-view {A}{B} A→B μA = mk searchᴮ ind
  where
    searchᴮ : Search B
    searchᴮ m f = search μA m (f ∘ A→B)

    ind : SearchInd searchᴮ
    ind P P∙ Pf = search-ind μA (λ s → P (λ f → s (f ∘ A→B))) P∙ (Pf ∘ A→B)

    {- derived from ind
    ext : SearchExt searchᴮ
    ext m f≗g = search-ext μA m (f≗g ∘ A→B)

    searchMonᴮ = searchMonFromSearch searchᴮ

    eps : Searchε searchMonᴮ
    eps = search-ε μA

    mono : SearchMono searchᴮ
    mono po ∙mono f≤°g = search-mono μA po ∙mono (f≤°g ∘ A→B)

    hom : SearchMonHom searchMonᴮ
    hom m f g = search-hom μA m (f ∘ A→B) (g ∘ A→B)

    swp : SearchSwap searchᴮ
    swp sg f hom = search-swap μA sg (f ∘ A→B) hom
    -}

μ-iso : ∀ {A B} → (A ↔ B) → SumProp A → SumProp B
μ-iso A↔B = μ-view (_⟨$⟩_ (Inverse.to A↔B))

μ-view-preserve : ∀ {A B} (A→B : A → B)(B→A : B → A)(A≈B : id ≗ B→A ∘ A→B) f (μA : SumProp A) → sum μA f ≡ sum (μ-view A→B μA) (f ∘ B→A)
μ-view-preserve A→B B→A A≈B f μA = sum-ext μA (≡.cong f ∘ A≈B)

μ-iso-preserve : ∀ {A B} (A↔B : A ↔ B) f (μA : SumProp A) → sum μA f ≡ sum (μ-iso A↔B μA) (f ∘ _⟨$⟩_ (Inverse.from A↔B))
μ-iso-preserve A↔B f μA = μ-view-preserve (_⟨$⟩_ (Inverse.to A↔B)) (_⟨$⟩_ (Inverse.from A↔B))
                            (≡.sym ∘ Inverse.left-inverse-of A↔B) f μA

open import Data.Fin hiding (_+_)
open import Data.Vec.NP as Vec renaming (map to vmap; sum to vsum; foldr to vfoldr)

vmsum : ∀ m {n} → let open Mon m in
                  Vec C n → C
vmsum m = vfoldr _ _∙_ ε
  where open Monoid m

searchMonFin : ∀ n → SearchMon (Fin n)
searchMonFin n m f = vmsum m (vmap f (allFin n)) -- or vsum (tabulate f)

searchFinSuc : ∀ n → Search (Fin (suc n))
searchFinSuc n _∙_ f = vfoldr _ _∙_ (f zero) (vmap (f ∘ suc) (allFin n))

sumFin : ∀ n → Sum (Fin n)
sumFin n f = vsum (vmap f (allFin n)) -- or vsum (tabulate f)

μMaybe : ∀ {A} → SumProp A → SumProp (Maybe A)
μMaybe μA = μ-iso (FI.sym Maybe↔⊤⊎) (μ⊤ +μ μA)

μMaybe^ : ∀ {A} n → SumProp A → SumProp (Maybe^ n A)
μMaybe^ zero    μA = μA
μMaybe^ (suc n) μA = μMaybe (μMaybe^ n μA)

μFin : ∀ n → SumProp (Fin (suc n))
μFin n = μ-iso (Maybe^⊤↔Fin1+ n) (μMaybe^ n μ⊤)
{-
μFin n = mk (searchFin n) ext eps hom sumFin-mon sumFin-swap
  module SumFin where
    ext : SearchMonExt (searchFin n)
    ext m f≗g = {!map-ext f≗g (allFin n)!}
      where open Mon m

    eps : Searchε (searchFin n)
    eps = {!!}

    hom : SearchMonHom (searchFin n)
    hom m f g = {!sum-linear f g (allFin n)!}

    sumFin-mon : SumMono (sumFin n)
    sumFin-mon f≤°g = sum-mono f≤°g (allFin n)

    sumFin-swap : SumSwap (sumFin n)
    sumFin-swap f {sumˣ} sumˣ-linear = inner (allFin n) where
      inner : ∀ {m}(xs : Vec (Fin n) m) → vsum (vmap (sumˣ ∘ f) xs) ≡ sumˣ (λ x → vsum (vmap (flip f x) xs))
      inner [] = ≡.sym (SumLinear.sum-lin sumˣ-linear (const 1337) 0)
      inner (x ∷ xs) rewrite inner xs = ≡.sym
                                          (SumLinear.sum-hom sumˣ-linear (f x)
                                                (λ y → vsum (vmap (flip f y) xs)))
-}

μVec : ∀ {A} (μA : SumProp A) n  → SumProp (Vec A n)
μVec μA zero    = μ-view (const []) μ⊤
μVec μA (suc n) = μ-view (uncurry _∷_) (μA ×μ μVec μA n)

{-
searchVec : ∀ {A} n → Search A → Search (Vec A n)
searchVec zero    searchᴬ m f = f []
searchVec (suc n) searchᴬ m f = searchᴬ m (λ x → searchVec n searchᴬ m (f ∘ _∷_ x))

sumVec : ∀ {A} n → Sum A → Sum (Vec A n)
sumVec n sumᴬ = searchVec n (λ m → {!sumᴬ!}) ℕ+.monoid

sumVec zero    sumᴬ f = f []
sumVec (suc n) sumᴬ f = (sumᴬ ×Sum sumVec n sumᴬ) (λ { (x , xs) → f (x ∷ xs) })

μVec' : ∀ {A} (μA : SumProp A) n  → SumProp (Vec A n)
μVec' {A} μA n = mk (searchVec n (search μA))  (mk (sumVec-lin n) (sumVec-hom n)) (sumVec-ext n) (sumVec-mon n) (sumVec-swap n)
  where
    sV = flip sumVec (sum μA)

    sumVec-ext : ∀ n → SumExt (sV n)
    sumVec-ext zero    f≗g = f≗g []
    sumVec-ext (suc n) f≗g = sum-ext μA (λ x → sumVec-ext n (f≗g ∘ _∷_ x))

    sumVec-lin : ∀ n → SumLin (sV n)
    sumVec-lin zero    f k = ≡.refl
    sumVec-lin (suc n) f k rewrite sum-ext μA (λ x → sumVec-lin n (f ∘ _∷_ x) k)
      = sum-lin μA (λ x → sV n (f ∘ _∷_ x)) k

    sumVec-hom : ∀ n → SumHom (sV n)
    sumVec-hom zero    f g = ≡.refl
    sumVec-hom (suc n) f g rewrite sum-ext μA (λ x → sumVec-hom n (f ∘ _∷_ x) (g ∘ _∷_ x))
      = sum-hom μA (λ x → sV n (f ∘ _∷_ x)) (λ x → sV n (g ∘ _∷_ x))

    sumVec-mon : ∀ n → SumMono (sV n)
    sumVec-mon zero    f≤°g = f≤°g []
    sumVec-mon (suc n) f≤°g = sum-mono μA (λ x → sumVec-mon n (f≤°g ∘ _∷_ x))

    sumVec-swap : ∀ n → SumSwap (sV n)
    sumVec-swap zero    f        μˣ-linear = ≡.refl
    sumVec-swap (suc n) f {sumˣ} μˣ-linear rewrite sum-ext μA (λ x → sumVec-swap n (f ∘ _∷_ x) μˣ-linear)
      = sum-swap μA (λ z x → sumVec n (sum μA) (λ y → f (z ∷ y) x)) μˣ-linear
-}

searchVec-++ : ∀ {A} n {m} (μA : SumProp A) sg
               → let open Sgrp sg in
                 (f : Vec A (n + m) → C)
               → search (μVec μA (n + m)) _∙_ f
               ≈ search (μVec μA n) _∙_ (λ xs → search (μVec μA m) _∙_
                  (λ ys → f (xs ++ ys)))
searchVec-++ zero    μA sg f = Sgrp.refl sg
searchVec-++ (suc n) μA sg f = search-ext μA sg (λ x →
                                  searchVec-++ n μA sg (f ∘ _∷_ x))

sumVec-swap : ∀ {A} n {m} (μA : SumProp A)(f : Vec A (n + m) → ℕ)
            → sum (μVec μA n) (λ xs → sum (μVec μA m) (λ ys → f (xs ++ ys)))
            ≡ sum (μVec μA m) (λ ys → sum (μVec μA n) (λ xs → f (xs ++ ys)))
sumVec-swap n {m} μA f = sum-swap (μVec μA n) (μVec μA m) (λ xs ys → f (xs ++ ys))

swapS : ∀ {A B} → SumProp (A × B) → SumProp (B × A)
swapS = μ-view Data.Product.swap
  -- μ-iso ×-comm

swapS-preserve : ∀ {A B} f (μA×B : SumProp (A × B)) → sum μA×B f ≡ sum (swapS μA×B) (f ∘ Data.Product.swap)
swapS-preserve f μA×B =  μ-view-preserve Data.Product.swap Data.Product.swap (λ x → ≡.refl) f μA×B {- or ≡.refl -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

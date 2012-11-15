module prefect-bintree where

import Data.Nat.NP as Nat
open Nat using (ℕ; zero; suc; 2^_; _+_; module ℕ°; module ℕ≤)
open import Data.Bits hiding (replicate; _<=_)
import Data.Bits.Search as Search
open Search.SimpleSearch
open import Function.NP
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≗_; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; uncurry) renaming (swap to swap-×)
open import Data.Vec.NP using (Vec; _++_; module Alternative-Reverse)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open Alternative-Reverse
open import Relation.Binary
import Level as L
open import Data.Bool
open import Algebra.FunctionProperties
import Relation.Binary.ToNat as ToNat
import Data.Bits.OperationSyntax as OperationSyntax

data Tree {a} (A : Set a) : ℕ → Set a where
  leaf : (x : A) → Tree A zero
  fork : ∀ {n} (left right : Tree A n) → Tree A (suc n)

data _∈_ {a}{A : Set a}(x : A) : {n : ℕ} → Tree A n → Set a where
  here  : x ∈ leaf x
  left  : {n : ℕ}{t₁ t₂ : Tree A n} → x ∈ t₁ → x ∈ fork t₁ t₂
  right : {n : ℕ}{t₁ t₂ : Tree A n} → x ∈ t₂ → x ∈ fork t₁ t₂

map : ∀ {n a b} {A : Set a} {B : Set b} → (A → B) → Tree A n → Tree B n
map f (leaf x)   = leaf (f x)
map f (fork t u) = fork (map f t) (map f u)

private
  module Dummy {a} {A : Set a} where
    replicate : ∀ n → A → Tree A n
    replicate zero    x = leaf x
    replicate (suc n) x = fork t t where t = replicate n x

    fromFun : ∀ {n} → (Bits n → A) → Tree A n
    fromFun {zero}  f = leaf (f [])
    fromFun {suc n} f = fork (fromFun (f ∘ 0∷_)) (fromFun (f ∘ 1∷_))

    toFun : ∀ {n} → Tree A n → Bits n → A
    toFun (leaf x)   _        = x
    toFun (fork t u) (b ∷ bs) = toFun (if b then u else t) bs

    toFun∘fromFun : ∀ {n} (f : Bits n → A) → toFun (fromFun f) ≗ f
    toFun∘fromFun {zero}  f [] = ≡.refl
    toFun∘fromFun {suc n} f (false ∷ xs)
      rewrite toFun∘fromFun (f ∘ 0∷_) xs = ≡.refl
    toFun∘fromFun {suc n} f (true ∷ xs)
      rewrite toFun∘fromFun (f ∘ 1∷_) xs = ≡.refl

    fromFun∘toFun : ∀ {n} (t : Tree A n) → fromFun (toFun t) ≡ t
    fromFun∘toFun (leaf x) = ≡.refl
    fromFun∘toFun (fork t₀ t₁)
      rewrite fromFun∘toFun t₀
            | fromFun∘toFun t₁ = ≡.refl

    toFun→fromFun : ∀ {n} (t : Tree A n) (f : Bits n → A) → toFun t ≗ f → t ≡ fromFun f
    toFun→fromFun (leaf x) f t≗f = ≡.cong leaf (t≗f [])
    toFun→fromFun (fork t₀ t₁) f t≗f
      rewrite toFun→fromFun t₀ _ (t≗f ∘ 0∷_)
            | toFun→fromFun t₁ _ (t≗f ∘ 1∷_) = ≡.refl

    fromFun→toFun : ∀ {n} (t : Tree A n) (f : Bits n → A) → t ≡ fromFun f → toFun t ≗ f
    fromFun→toFun ._ _ ≡.refl = toFun∘fromFun _

    fromFun-≗ : ∀ {n} {f g : Bits n → A} → f ≗ g → fromFun f ≡ fromFun g
    fromFun-≗ {zero}  f≗g
      rewrite f≗g [] = ≡.refl
    fromFun-≗ {suc n} f≗g
      rewrite fromFun-≗ (f≗g ∘ 0∷_)
            | fromFun-≗ (f≗g ∘ 1∷_)
            = ≡.refl

    lookup : ∀ {n} → Bits n → Tree A n → A
    lookup = flip toFun

    lft : ∀ {n} → Tree A (1 + n) → Tree A n
    lft (fork t _) = t

    rght : ∀ {n} → Tree A (1 + n) → Tree A n
    rght (fork _ t) = t

    ηfork : ∀ {n} (t : Tree A (1 + n)) → t ≡ fork (lft t) (rght t)
    ηfork (fork _ _) = ≡.refl

    from-× : A × A → Tree A 1
    from-× (x , y) = fork (leaf x) (leaf y)

    to-× : Tree A 1 → A × A
    to-× (fork (leaf x) (leaf y)) = x , y

    swap : ∀ {n} → Tree A (1 + n) → Tree A (1 + n)
    swap t = fork (rght t) (lft t)

    map-inner : ∀ {n} → (Tree A (1 + n) → Tree A (1 + n)) → (Tree A (2 + n) → Tree A (2 + n))
    map-inner f (fork (fork t₀ t₁) (fork t₂ t₃)) =
      case f (fork t₁ t₂) of λ { (fork t₄ t₅) → fork (fork t₀ t₄) (fork t₅ t₃) }

    map-outer : ∀ {n} → (f g : Tree A n → Tree A n) → (Tree A (1 + n) → Tree A (1 + n))
    map-outer f g (fork t u) = fork (f t) (g u)

    interchange : ∀ {n} → Tree A (2 + n) → Tree A (2 + n)
    interchange = map-inner swap

    inner : ∀ {n} → Tree A (2 + n) → Tree A (1 + n)
    inner t = fork (rght (lft t)) (lft (rght t))

    first : ∀ {n} → Tree A n → A
    first (leaf x)   = x
    first (fork t _) = first t

    last : ∀ {n} → Tree A n → A
    last (leaf x)   = x
    last (fork _ t) = last t

    -- Returns the flat vector of leaves underlying the perfect binary tree.
    toVec : ∀ {n} → Tree A n → Vec A (2^ n)
    toVec (leaf x)     = x ∷ []
    toVec (fork t₀ t₁) = toVec t₀ ++ toVec t₁

    lookup' : ∀ {m n} → Bits m → Tree A (m + n) → Tree A n
    lookup' [] t = t
    lookup' (b ∷ bs) (fork t t₁) = lookup' bs (if b then t₁ else t)

    update' : ∀ {m n} → Bits m → Tree A n → Tree A (m + n) → Tree A (m + n)
    update' []        val t = val
    update' (b ∷ key) val (fork t u) = if b then fork t (update' key val u)
                                            else fork (update' key val t) u

    ∈-toBits : ∀ {x n} {t : Tree A n} → x ∈ t → Bits n
    ∈-toBits here = []
    ∈-toBits (left key) = 0b ∷ ∈-toBits key
    ∈-toBits (right key) = 1b ∷ ∈-toBits key

    ∈-lookup : ∀ {x n} {t : Tree A n} (path : x ∈ t) → lookup (∈-toBits path) t ≡ x
    ∈-lookup here = ≡.refl
    ∈-lookup (left path) = ∈-lookup path
    ∈-lookup (right path) = ∈-lookup path

    lookup-∈ : ∀ {n} key (t : Tree A n) → lookup key t ∈ t
    lookup-∈ [] (leaf x) = here
    lookup-∈ (true ∷ key) (fork tree tree₁) = right (lookup-∈ key tree₁)
    lookup-∈ (false ∷ key) (fork tree tree₁) = left (lookup-∈ key tree)

open Dummy public

module Fold {a b i} {I : Set i} (ze : I) (su : I → I)
            {A : Set a} {B : I → Set b}
            (f : A → B ze) (_·_ : ∀ {n} → B n → B n → B (su n)) where

  `_ : ℕ → I
  `_ = Nat.fold ze su

  fold : ∀ {n} → Tree A n → B(` n)
  fold (leaf x)    = f x
  fold (fork t₀ t₁) = fold t₀ · fold t₁

fold : ∀ {n a} {A : Set a} (op : A → A → A) → Tree A n → A
fold {A = A} op = Fold.fold 0 suc {B = const A} id op

search≡fold∘fromFun : ∀ {n a} {A : Set a} op (f : Bits n → A) → search op f ≡ fold op (fromFun f)
search≡fold∘fromFun {zero}  op f = ≡.refl
search≡fold∘fromFun {suc n} op f
  rewrite search≡fold∘fromFun op (f ∘ 0∷_)
        | search≡fold∘fromFun op (f ∘ 1∷_) = ≡.refl

module FoldProp {a ℓ} {A : Set a} (_Ⓧ_ : Set ℓ → Set ℓ → Set ℓ) where
    Fold : ∀ {n} → (Bits n → A → Set ℓ) → Tree A n → Set ℓ
    Fold f (leaf x)     = f [] x
    Fold f (fork t₀ t₁) = Fold (f ∘ 0∷_) t₀ Ⓧ Fold (f ∘ 1∷_) t₁

All : ∀ {n a} {A : Set a} → (Bits n → A → Set) → Tree A n → Set
All = FoldProp.Fold _×_

Any : ∀ {n a} {A : Set a} → (Bits n → A → Set) → Tree A n → Set
Any = FoldProp.Fold _⊎_

module AllBits where
  _IsRevPrefixOf_ : ∀ {m n} → Bits m → Bits (rev-+ m n) → Set
  _IsRevPrefixOf_ {m} {n} p xs = ∃ λ (ys : Bits n) → rev-app p ys ≡ xs

  RevPrefix : ∀ {m n o} (p : Bits m) → Tree (Bits (rev-+ m n)) o → Set
  RevPrefix p = All (λ _ → _IsRevPrefixOf_ p)

  RevPrefix-[]-⊤ : ∀ {m n} (t : Tree (Bits m) n) → RevPrefix [] t
  RevPrefix-[]-⊤ (leaf x) = x , ≡.refl
  RevPrefix-[]-⊤ (fork t u) = RevPrefix-[]-⊤ t , RevPrefix-[]-⊤ u

  All-fromFun : ∀ {m} n (p : Bits m) → All (_≡_ ∘ rev-app p) (fromFun {n = n} (rev-app p))
  All-fromFun zero    p = ≡.refl
  All-fromFun (suc n) p = All-fromFun n (0∷ p) , All-fromFun n (1∷ p)

  All-id : ∀ n → All {n} _≡_ (fromFun id)
  All-id n = All-fromFun n []

module SortedDataIx {a ℓ} {A : Set a} (_≤ᴬ_ : A → A → Set ℓ) (isPreorder : IsPreorder _≡_ _≤ᴬ_) where
    data Sorted : ∀ {n} → Tree A n → A → A → Set (a L.⊔ ℓ) where
      leaf : {x : A} → Sorted (leaf x) x x
      fork : ∀ {n} {t u : Tree A n} {low_t high_t lowᵤ highᵤ} →
             Sorted t low_t high_t →
             Sorted u lowᵤ highᵤ →
             (h≤l : high_t ≤ᴬ lowᵤ) →
             Sorted (fork t u) low_t highᵤ

    private
        module ≤ᴬ = IsPreorder isPreorder

    ≤ᴬ-bounds : ∀ {n} {t : Tree A n} {l h} → Sorted t l h → l ≤ᴬ h
    ≤ᴬ-bounds leaf            = ≤ᴬ.refl
    ≤ᴬ-bounds (fork s₀ s₁ pf) = ≤ᴬ.trans (≤ᴬ-bounds s₀) (≤ᴬ.trans pf (≤ᴬ-bounds s₁))

    Sorted→lb : ∀ {n} {t : Tree A n} {l h} → Sorted t l h → ∀ {x} → x ∈ t → l ≤ᴬ x
    Sorted→lb leaf            here      = ≤ᴬ.refl
    Sorted→lb (fork s _ _)    (left  p) = Sorted→lb s p
    Sorted→lb (fork s₀ s₁ pf) (right p) = ≤ᴬ.trans (≤ᴬ.trans (≤ᴬ-bounds s₀) pf) (Sorted→lb s₁ p)

    Sorted→ub : ∀ {n} {t : Tree A n} {l h} → Sorted t l h → ∀ {x} → x ∈ t → x ≤ᴬ h
    Sorted→ub leaf            here      = ≤ᴬ.refl
    Sorted→ub (fork _ s _)    (right p) = Sorted→ub s p
    Sorted→ub (fork s₀ s₁ pf) (left  p) = ≤ᴬ.trans (≤ᴬ.trans (Sorted→ub s₀ p) pf) (≤ᴬ-bounds s₁)

    Bounded : ∀ {n} → Tree A n → A → A → Set (a L.⊔ ℓ)
    Bounded t l h = ∀ {x} → x ∈ t → (l ≤ᴬ x) × (x ≤ᴬ h)

    Sorted→Bounded : ∀ {n} {t : Tree A n} {l h} → Sorted t l h → Bounded t l h
    Sorted→Bounded s x = Sorted→lb s x , Sorted→ub s x

    first-lb : ∀ {n} {t : Tree A n} {l h} → Sorted t l h → first t ≡ l
    first-lb leaf          = ≡.refl
    first-lb (fork st _ _) = first-lb st

    last-ub : ∀ {n} {t : Tree A n} {l h} → Sorted t l h → last t ≡ h
    last-ub leaf          = ≡.refl
    last-ub (fork _ st _) = last-ub st

    uniq-lb : ∀ {n} {t : Tree A n} {l₀ h₀ l₁ h₁}
                  → Sorted t l₀ h₀ → Sorted t l₁ h₁ → l₀ ≡ l₁
    uniq-lb leaf leaf = ≡.refl
    uniq-lb (fork p p₁ h≤l) (fork q q₁ h≤l₁) = uniq-lb p q

    uniq-ub : ∀ {n} {t : Tree A n} {l₀ h₀ l₁ h₁}
                  → Sorted t l₀ h₀ → Sorted t l₁ h₁ → h₀ ≡ h₁
    uniq-ub leaf leaf = ≡.refl
    uniq-ub (fork p p₁ h≤l) (fork q q₁ h≤l₁) = uniq-ub p₁ q₁

    Sorted-trans : ∀ {n} {t u v : Tree A n} {lt hu lu hv}
                   → Sorted (fork t u) lt hu → Sorted (fork u v) lu hv → Sorted (fork t v) lt hv
    Sorted-trans {lt = lt} {hu} {lu} {hv} (fork tu tu₁ h≤l) (fork uv uv₁ h≤l₁)
       rewrite uniq-lb uv tu₁
             | uniq-ub uv tu₁
         = fork tu uv₁ (≤ᴬ.trans h≤l (≤ᴬ.trans (≤ᴬ-bounds tu₁) h≤l₁))

module SortedData {a ℓ} {A : Set a} (_≤ᴬ_ : A → A → Set ℓ) (isPreorder : IsPreorder _≡_ _≤ᴬ_) where
    data Sorted : ∀ {n} → Tree A n → Set (a L.⊔ ℓ) where
      leaf : {x : A} → Sorted (leaf x)
      fork : ∀ {n} {t u : Tree A n} →
             Sorted t →
             Sorted u →
             (h≤l : last t ≤ᴬ first u) →
             Sorted (fork t u)

    PreSorted : ∀ {n} → Tree A (1 + n) → Set _
    PreSorted t = Sorted (lft t) × Sorted (rght t)

    private
        module ≤ᴬ = IsPreorder isPreorder

    ≤ᴬ-bounds : ∀ {n} {t : Tree A n} → Sorted t → first t ≤ᴬ last t
    ≤ᴬ-bounds leaf            = ≤ᴬ.refl
    ≤ᴬ-bounds (fork s₀ s₁ pf) = ≤ᴬ.trans (≤ᴬ-bounds s₀) (≤ᴬ.trans pf (≤ᴬ-bounds s₁))

    Sorted→lb : ∀ {n} {t : Tree A n} → Sorted t → ∀ (p : Bits n) → first t ≤ᴬ lookup p t
    Sorted→lb leaf             []          = ≤ᴬ.refl
    Sorted→lb (fork st su h≤l) (true  ∷ p) = ≤ᴬ.trans (≤ᴬ.trans (≤ᴬ-bounds st) h≤l) (Sorted→lb su p)
    Sorted→lb (fork st _  _)   (false ∷ p) = Sorted→lb st p

    Sorted→ub : ∀ {n} {t : Tree A n} → Sorted t → ∀ (p : Bits n) → lookup p t ≤ᴬ last t
    Sorted→ub leaf             []          = ≤ᴬ.refl
    Sorted→ub (fork _  su _)   (true  ∷ p) = Sorted→ub su p
    Sorted→ub (fork st su h≤l) (false ∷ p) = ≤ᴬ.trans (≤ᴬ.trans (Sorted→ub st p) h≤l) (≤ᴬ-bounds su)

    Bounded : ∀ {n} → Tree A n → A → A → Set ℓ
    Bounded {n} t l h = ∀ (p : Bits n) → (l ≤ᴬ lookup p t) × (lookup p t ≤ᴬ h)

    Sorted→Bounded : ∀ {n} {t : Tree A n} → Sorted t → Bounded t (first t) (last t)
    Sorted→Bounded s x = Sorted→lb s x , Sorted→ub s x

module SortedMembershipProofs {a ℓ} {A : Set a} (_≤ᴬ_ : A → A → Set ℓ)
                              (isPreorder : IsPreorder _≡_ _≤ᴬ_) where

    _≤ᴾ_ : ∀ {n x y} {t : Tree A n} → x ∈ t → y ∈ t → Set
    p ≤ᴾ q = ∈-toBits p ≤ᴮ ∈-toBits q

    Sorted : ∀ {n} → Tree A n → Set _
    Sorted t = ∀ {x} (p : x ∈ t) {y} (q : y ∈ t) → p ≤ᴾ q → x ≤ᴬ y

    private
        module ≤ᴬ = IsPreorder isPreorder

    module S = SortedDataIx _≤ᴬ_ isPreorder
    open S using (leaf; fork)
    Sorted→Sorted' : ∀ {n l h} {t : Tree A n} → S.Sorted t l h → Sorted t
    Sorted→Sorted' leaf             here     here       p≤q = ≤ᴬ.refl
    Sorted→Sorted' (fork s _ _)     (left p) (left q)   (there ._ p≤q) = Sorted→Sorted' s p q p≤q
    Sorted→Sorted' (fork s₀ s₁ l≤h) (left p) (right q)  p≤q = ≤ᴬ.trans (S.Sorted→ub s₀ p) (≤ᴬ.trans l≤h (S.Sorted→lb s₁ q))
    Sorted→Sorted' (fork _ _ _)     (right _) (left _)  ()
    Sorted→Sorted' (fork _ s _)     (right p) (right q) (there ._ p≤q) = Sorted→Sorted' s p q p≤q

module SortedMonotonicFunctions {a ℓ} {A : Set a} (_≤ᴬ_ : A → A → Set ℓ)
                                (isPreorder : IsPreorder _≡_ _≤ᴬ_) where

    Monotone : ∀ {n} → (Bits n → A) → Set _
    Monotone {n} f = ∀ {p q : Bits n} → p ≤ᴮ q → f p ≤ᴬ f q

    Sorted : ∀ {n} → Tree A n → Set _
    Sorted = Monotone ∘ toFun

    private
        module ≤ᴬ = IsPreorder isPreorder

    open SortedData _≤ᴬ_ isPreorder renaming (Sorted to DataSorted)
    DataSorted→Sorted : ∀ {n} {t : Tree A n} → DataSorted t → Sorted t
    DataSorted→Sorted leaf             []                = ≤ᴬ.refl
    DataSorted→Sorted (fork _  su _)   (there true  p≤q) = DataSorted→Sorted su p≤q
    DataSorted→Sorted (fork st _  _)   (there false p≤q) = DataSorted→Sorted st p≤q
    DataSorted→Sorted (fork st su h≤l) (0-1 p q)         = ≤ᴬ.trans (≤ᴬ.trans (Sorted→ub st p) h≤l) (Sorted→lb su q)

module Sorting-⊓-⊔ {a} {A : Set a} (_⊓ᴬ_ _⊔ᴬ_ : A → A → A) where

    sort-× : Endo (A × A)
    sort-× (x , y) = (x ⊓ᴬ y , x ⊔ᴬ y)

    sort₁ : Endo (Tree A 1)
    sort₁ = from-× ∘ sort-× ∘ to-×

    merge : ∀ {n} → Endo (Tree A (1 + n))
    merge {zero}  = sort₁
    merge {suc _} = map-inner merge ∘ map-outer merge merge ∘ interchange

    sort : ∀ {n} → Tree A n → Tree A n
    sort {zero}  = id
    sort {suc _} = merge ∘ map-outer sort sort

module ⊓-⊔ᴬ {a} {A : Set a} (_<=ᴬ_ : A → A → Bool) where
    _⊓ᴬ_ : A → A → A
    x ⊓ᴬ y = if x <=ᴬ y then x else y
    _⊔ᴬ_ : A → A → A
    x ⊔ᴬ y = if x <=ᴬ y then y else x

module Sorting-<= {a} {A : Set a} (_<=ᴬ_ : A → A → Bool) where
    open ⊓-⊔ᴬ _<=ᴬ_
    open Sorting-⊓-⊔ _⊓ᴬ_ _⊔ᴬ_ public

module EvalTree {a} {A : Set a} where
    open OperationSyntax renaming (map-inner to `map-inner; map-outer to `map-outer)
    evalTree : ∀ {n} → Bij n → Endo (Tree A n)
    evalTree `id          = id
    evalTree (f `⁏ g)      = evalTree g ∘ evalTree f
    evalTree (`id   `∷ f) = map-outer (evalTree (f 0b)) (evalTree (f 1b))
    evalTree (`notᴮ `∷ f) = map-outer (evalTree (f 1b)) (evalTree (f 0b)) ∘ swap
    evalTree `0↔1         = interchange

    evalTree-eval : ∀ {n} (f : Bij n) (t : Tree A n) → toFun t ≗ toFun (evalTree f t) ∘ eval f
    evalTree-eval `id  _ _ = ≡.refl
    evalTree-eval `0↔1 (fork (fork _ _) (fork _ _)) (true  ∷ true  ∷ _) = ≡.refl
    evalTree-eval `0↔1 (fork (fork _ _) (fork _ _)) (false ∷ true  ∷ _) = ≡.refl
    evalTree-eval `0↔1 (fork (fork _ _) (fork _ _)) (true  ∷ false ∷ _) = ≡.refl
    evalTree-eval `0↔1 (fork (fork _ _) (fork _ _)) (false ∷ false ∷ _) = ≡.refl
    evalTree-eval (f `⁏ g) t xs
      rewrite evalTree-eval f t xs
            | evalTree-eval g (evalTree f t) (eval f xs)
            = ≡.refl
    evalTree-eval (`id   `∷ f) (fork t u) (true  ∷ xs) = evalTree-eval (f 1b) u xs
    evalTree-eval (`id   `∷ f) (fork t u) (false ∷ xs) = evalTree-eval (f 0b) t xs
    evalTree-eval (`notᴮ `∷ f) (fork t u) (true  ∷ xs) = evalTree-eval (f 1b) u xs
    evalTree-eval (`notᴮ `∷ f) (fork t u) (false ∷ xs) = evalTree-eval (f 0b) t xs

    evalTree-eval′ : ∀ {n} (f : Bij n) (t : Tree A n) → toFun (evalTree f t) ≗ toFun t ∘ eval (f ⁻¹)
    evalTree-eval′ f t x = toFun (evalTree f t) x
                         ≡⟨ ≡.cong (toFun (evalTree f t)) (≡.sym (VecBijKit._⁻¹-inverse′ _ f x)) ⟩
                           toFun (evalTree f t) (eval f (eval (f ⁻¹) x))
                         ≡⟨ ≡.sym (evalTree-eval f t (eval (f ⁻¹) x)) ⟩
                           toFun t (eval (f ⁻¹) x)
                         ∎ where open ≡-Reasoning

module BijSpec {a} {A : Set a} where
    open EvalTree
    open OperationSyntax renaming (map-inner to `map-inner; map-outer to `map-outer)

    record Bij[_↦_] {n} (t u : Tree A n) : Set a where
      constructor _,_
      field
        bij   : Bij n
        proof : evalTree bij t ≡ u
    open Bij[_↦_] public

    Bij[≗_] : ∀ {n} (f : Endo (Tree A n)) → Set a
    Bij[≗ f ] = ∀ t → Bij[ t ↦ f t ]

    evalB : ∀ {n} {f : Endo (Tree A n)} (b : Bij[≗ f ]) → Endo (Tree A n)
    evalB b t = evalTree (bij (b t)) t

    bij-evalB-spec : ∀ {n} {f : Endo (Tree A n)} (b : Bij[≗ f ]) → evalB b ≗ f
    bij-evalB-spec b = proof ∘ b

    id-bij : ∀ {n} → Bij[≗ id {A = Tree A n} ]
    id-bij _ = `id , ≡.refl

    infixr 9 _∘-bij_
    _∘-bij_ : ∀ {n} {f g : Endo (Tree A n)} → Bij[≗ f ] → Bij[≗ g ] → Bij[≗ f ∘ g ]
    _∘-bij_ {f = f} {g} `f `g t
      = `bij , helper
      where `bij = bij (`g t) `⁏ bij (`f (g t))
            helper : evalTree `bij t ≡ f (g t)
            helper rewrite proof (`g t) = proof (`f (g t))

    swap-bij : ∀ {n} → Bij[≗ swap {n = n} ]
    swap-bij (fork _ _) = `not , ≡.refl

    map-outer-bij : ∀ {n} {f g : Endo (Tree A n)}
                      → Bij[≗ f ] → Bij[≗ g ] → Bij[≗ map-outer f g ]
    map-outer-bij `f `g (fork t u)
      = `map-outer (bij (`f t)) (bij (`g u))
      , ≡.cong₂ fork (proof (`f t)) (proof (`g u))

    map-inner-bij : ∀ {n} {f : Endo (Tree A (1 + n))} → Bij[≗ f ] → Bij[≗ map-inner f ]
    map-inner-bij {f = f} `f t = map-inner-perm , helper
       where map-inner-perm = `map-inner (bij (`f (inner t)))
             helper : evalTree map-inner-perm t ≡ map-inner f t
             helper with t
             ... | fork (fork a b) (fork c d) with f (fork b c) | proof (`f (fork b c))
             ... | fork B C | p rewrite p = ≡.refl

    interchange-bij : ∀ {n} → Bij[≗ interchange {n = n} ]
    interchange-bij = map-inner-bij swap-bij

module SortingBijSpec {a} {A : Set a} (_<=ᴬ_ : A → A → Bool)
                      (isTotalOrder : IsTotalOrder _≡_ (λ x y → T (x <=ᴬ y)))
    where
    open IsTotalOrder isTotalOrder

    open Sorting-<= _<=ᴬ_
    open EvalTree
    open OperationSyntax
    open BijSpec

    `sort₁ : Tree A 1 → Bij 1
    `sort₁ = `xor ∘ uncurry _<=ᴬ_ ∘ swap-× ∘ to-×

    sort₁-bij : Bij[≗ sort₁ ]
    sort₁-bij t = `sort₁ t , helper t
      where helper : ∀ t → evalTree (`sort₁ t) t ≡ sort₁ t
            helper (fork (leaf x) (leaf y)) with y <=ᴬ x | x <=ᴬ y | antisym {x} {y} | total x y
            ... | true  | true  | p | _ rewrite p _ _ = ≡.refl
            ... | false | true  | _ | _ = ≡.refl
            ... | true  | false | _ | _ = ≡.refl
            ... | false | false | _ | inj₁ ()
            ... | false | false | _ | inj₂ ()

    merge-bij : ∀ {n} → Bij[≗ merge {n} ]
    merge-bij {zero}  = sort₁-bij
    merge-bij {suc _} = map-inner-bij merge-bij
                  ∘-bij map-outer-bij merge-bij merge-bij
                  ∘-bij interchange-bij

    sort-bij : ∀ {n} → Bij[≗ sort {n} ]
    sort-bij {zero}  = id-bij
    sort-bij {suc _} = merge-bij ∘-bij map-outer-bij sort-bij sort-bij

module MergeSwap {a} {A : Set a}
                 (_⊓ᴬ_ _⊔ᴬ_ : A → A → A)
                 (⊓-comm : Commutative _≡_ _⊓ᴬ_)
                 (⊔-comm : Commutative _≡_ _⊔ᴬ_) where
    open Sorting-⊓-⊔ _⊓ᴬ_ _⊔ᴬ_
    merge-swap : ∀ {n} (t : Tree A (1 + n)) → merge t ≡ merge (swap t)
    merge-swap (fork (leaf x) (leaf y)) rewrite ⊔-comm x y | ⊓-comm y x = ≡.refl
    merge-swap (fork (fork t₀ t₁) (fork u₀ u₁))
      rewrite merge-swap (fork t₀ u₀)
            | merge-swap (fork t₁ u₁) = ≡.refl

module SortingDataIxProperties {ℓ a} {A : Set a} (_≤ᴬ_ : A → A → Set ℓ)
                               (_⊓ᴬ_ _⊔ᴬ_ : A → A → A)
                               (isPreorder : IsPreorder _≡_ _≤ᴬ_)
                               (⊔-spec : ∀ {x y} → x ≤ᴬ y → x ⊔ᴬ y ≡ y)
                               (⊓-spec : ∀ {x y} → x ≤ᴬ y → x ⊓ᴬ y ≡ x)
                               (⊓-comm : Commutative _≡_ _⊓ᴬ_)
                               (⊔-comm : Commutative _≡_ _⊔ᴬ_)
                               where
    open MergeSwap _⊓ᴬ_ _⊔ᴬ_ ⊓-comm ⊔-comm
    module ≤ᴬ = IsPreorder isPreorder
    open SortedDataIx _≤ᴬ_ isPreorder
    open Sorting-⊓-⊔ _⊓ᴬ_ _⊔ᴬ_

    {-# NO_TERMINATION_CHECK #-} -- needed due to a bug in Termination/SparseMatrix.hs blowUpSparseVector
    merge-pres : ∀ {n} {t : Tree A (1 + n)} {l h} → Sorted t l h → merge t ≡ t
    merge-pres (fork leaf leaf x) = ≡.cong₂ (fork on leaf) (⊓-spec x) (⊔-spec x)
    merge-pres {t = fork (fork t₀ t₁) (fork u₀ u₁)}
               (fork (fork {low_t = lt₀} {ht₀} {lt₁} {ht₁} st₀ st₁ ht₀≤lt₁)
                     (fork {low_t = lu₀} {hu₀} {lu₁} {hu₁} su₀ su₁ hu₀≤lu₁) ht₁≤lu₀)
       rewrite merge-pres (fork st₀ su₀ (≤ᴬ.trans ht₀≤lt₁ (≤ᴬ.trans (≤ᴬ-bounds st₁) ht₁≤lu₀)))
             | merge-pres (fork st₁ su₁ (≤ᴬ.trans ht₁≤lu₀ (≤ᴬ.trans (≤ᴬ-bounds su₀) hu₀≤lu₁)))
             | merge-swap (fork u₀ t₁)
             | merge-pres (fork st₁ su₀ ht₁≤lu₀) = ≡.refl

module SortingProperties {ℓ a} {A : Set a} (_≤ᴬ_ : A → A → Set ℓ)
                               (_⊓ᴬ_ _⊔ᴬ_ : A → A → A)
                               (isPreorder : IsPreorder _≡_ _≤ᴬ_)
                               (≤-⊔ : ∀ x y → x ≤ᴬ (y ⊔ᴬ x))
                               (⊓-≤ : ∀ x y → (x ⊓ᴬ y) ≤ᴬ y)
                               (≤-<_,_> : ∀ {x y z} → x ≤ᴬ y → x ≤ᴬ z → x ≤ᴬ (y ⊓ᴬ z))
                               (≤-[_,_] : ∀ {x y z} → x ≤ᴬ z → y ≤ᴬ z → (x ⊔ᴬ y) ≤ᴬ z)
                               (≤-⊓₀ : ∀ {x y z} → x ≤ᴬ (y ⊓ᴬ z) → x ≤ᴬ y)
                               (≤-⊓₁ : ∀ {x y z} → x ≤ᴬ (y ⊓ᴬ z) → x ≤ᴬ z)
                               (≤-⊔₀ : ∀ {x y z} → (x ⊔ᴬ y) ≤ᴬ z → x ≤ᴬ z)
                               (≤-⊔₁ : ∀ {x y z} → (x ⊔ᴬ y) ≤ᴬ z → y ≤ᴬ z)
                               where
    module ≤ᴬ = IsPreorder isPreorder
    open Sorting-⊓-⊔ _⊓ᴬ_ _⊔ᴬ_
    module SD = SortedData _≤ᴬ_ isPreorder
    open SD using (fork; leaf; PreSorted)

    first-merge : ∀ {n} (t : Tree A (1 + n)) →
                first (merge t) ≡ first (lft t) ⊓ᴬ first (rght t)
    first-merge (fork (leaf x) (leaf y)) = ≡.refl
    first-merge (fork (fork t₀ t₁) (fork u₀ u₁))
      with merge (fork t₀ u₀) | first-merge (fork t₀ u₀)
         | merge (fork t₁ u₁)
    ... | fork v₀ w₀ | pf
        | fork v₁ w₁
      with merge (fork w₀ v₁)
    ... | fork a b
      = pf

    last-merge : ∀ {n} (t : Tree A (1 + n)) →
                last (merge t) ≡ last (lft t) ⊔ᴬ last (rght t)
    last-merge (fork (leaf x) (leaf y)) = ≡.refl
    last-merge (fork (fork t₀ t₁) (fork u₀ u₁))
      with merge (fork t₀ u₀)
         | merge (fork t₁ u₁) | last-merge (fork t₁ u₁)
    ... | fork v₀ w₀
        | fork v₁ w₁ | pf
      with merge (fork w₀ v₁)
    ... | fork a b
      = pf

    merge-spec′ : ∀ {n} {t u : Tree A n} →
                 SD.Sorted t → SD.Sorted u →
                 let tu' = merge (fork t u) in
                 SD.Sorted tu'
                 × last (lft tu') ≤ᴬ (last t ⊓ᴬ last u)
                 × (first t ⊔ᴬ first u) ≤ᴬ first (rght tu')
    merge-spec′ (leaf {x}) (leaf {y}) = fork leaf leaf (≤ᴬ.trans (⊓-≤ x y) (≤-⊔ y x)) , ≤ᴬ.refl , ≤ᴬ.refl
    merge-spec′ {t = fork t₀ t₁} {u = fork u₀ u₁}
               (fork st₀ st₁ ht₀≤lt₁)
               (fork su₀ su₁ lu₀≤hu₁)
      with merge (fork t₀ u₀) | merge-spec′ st₀ su₀ | last-merge (fork t₀ u₀)
         | merge (fork t₁ u₁) | merge-spec′ st₁ su₁ | first-merge (fork t₁ u₁)
    ... | fork v₀ w₀ | (fork sv₀ sw₀ p1 , lpf1 , rpf1) | lastw₀
        | fork v₁ w₁ | (fork sv₁ sw₁ p2 , lpf2 , rpf2) | firstv₁
      with merge (fork w₀ v₁) | merge-spec′ sw₀ sv₁ | first-merge (fork w₀ v₁) | last-merge (fork w₀ v₁)
    ... | fork a b | (fork sa sb p3 , lpf3 , rpf3) | firsta | lastb
      = fork (fork sv₀ sa pf1) (fork sb sw₁ pf2) p3 , lpf4 , rpf4
         where
             pf1 : last v₀ ≤ᴬ first a
             pf1 rewrite firsta | firstv₁ = ≤-< p1 , ≤-< ≤ᴬ.trans (≤-⊓₀ lpf1) ht₀≤lt₁ , ≤ᴬ.trans (≤-⊓₁ lpf1) lu₀≤hu₁ > >
             pf2 : last b ≤ᴬ first w₁
             pf2 rewrite lastb | lastw₀ = ≤-[ ≤-[ ≤ᴬ.trans ht₀≤lt₁ (≤-⊔₀ rpf2) , ≤ᴬ.trans lu₀≤hu₁ (≤-⊔₁ rpf2) ] , p2 ]
             lpf4 = ≤-< ≤ᴬ.trans (≤-⊓₁ lpf3) (≤-⊓₀ lpf2) , ≤ᴬ.trans (≤-⊓₁ lpf3) (≤-⊓₁ lpf2) >
             rpf4 = ≤-[ ≤ᴬ.trans (≤-⊔₀ rpf1) (≤-⊔₀ rpf3) , ≤ᴬ.trans (≤-⊔₁ rpf1) (≤-⊔₀ rpf3) ]

    merge-spec : ∀ {n} {t : Tree A (1 + n)} → PreSorted t → SD.Sorted (merge t)
    merge-spec {t = fork t u} (st , su) = proj₁ (merge-spec′ st su)

    sort-spec : ∀ {n} (t : Tree A n) → SD.Sorted (sort t)
    sort-spec (leaf _)   = leaf
    sort-spec (fork t u) = merge-spec (sort-spec t , sort-spec u)

module FunctionSorting {a} {A : Set a} (_<=ᴬ_ : A → A → Bool) where
  _≤ᴬ_ = λ x y → T (x <=ᴬ y)
  open ⊓-⊔ᴬ _<=ᴬ_
  module S = Sorting-<= _<=ᴬ_
  open BijSpec

  sort : ∀ {n} → Endo (Bits n → A)
  sort = toFun ∘ S.sort ∘ fromFun

  module Properties (isTotalOrder : IsTotalOrder _≡_ (λ x y → T (x <=ᴬ y)))
                    (≤-⊔ : ∀ x y → x ≤ᴬ (y ⊔ᴬ x))
                    (⊓-≤ : ∀ x y → (x ⊓ᴬ y) ≤ᴬ y)
                    (≤-<_,_> : ∀ {x y z} → x ≤ᴬ y → x ≤ᴬ z → x ≤ᴬ (y ⊓ᴬ z))
                    (≤-[_,_] : ∀ {x y z} → x ≤ᴬ z → y ≤ᴬ z → (x ⊔ᴬ y) ≤ᴬ z)
                    (≤-⊓₀ : ∀ {x y z} → x ≤ᴬ (y ⊓ᴬ z) → x ≤ᴬ y)
                    (≤-⊓₁ : ∀ {x y z} → x ≤ᴬ (y ⊓ᴬ z) → x ≤ᴬ z)
                    (≤-⊔₀ : ∀ {x y z} → (x ⊔ᴬ y) ≤ᴬ z → x ≤ᴬ z)
                    (≤-⊔₁ : ∀ {x y z} → (x ⊔ᴬ y) ≤ᴬ z → y ≤ᴬ z) where

    module B = SortingBijSpec _<=ᴬ_  isTotalOrder
    open IsTotalOrder isTotalOrder
    open SortedMonotonicFunctions _≤ᴬ_ isPreorder
    module SP = SortingProperties _≤ᴬ_ _⊓ᴬ_ _⊔ᴬ_ isPreorder
                   ≤-⊔ ⊓-≤ ≤-<_,_> ≤-[_,_] ≤-⊓₀ ≤-⊓₁ ≤-⊔₀ ≤-⊔₁
    open OperationSyntax using (eval; Bij)
    open EvalTree

    sort-is-sorting : ∀ {n} (f : Bits n → A) → Monotone (sort f)
    sort-is-sorting = DataSorted→Sorted ∘ SP.sort-spec ∘ fromFun

module BitsSorting {m} where
    open ToNat {A = Bits m} toℕ (λ {x} {y} → toℕ-inj x y) public

    module S = Sorting-⊓-⊔ _⊓_ _⊔_
    module SDP = SortingDataIxProperties _≤_ _⊓_ _⊔_ isPreorder (λ {x} {y} z → ⊔-spec {x} {y} z)
                   (λ {x} {y} → ⊓-spec {x} {y}) ⊓-comm ⊔-comm
    module SP = SortingProperties _≤_ _⊓_ _⊔_ isPreorder
                   ≤-⊔ ⊓-≤
                   (λ {x} {y} {z} → ≤-<_,_> {x} {y} {z})
                   (λ {x} {y} {z} → ≤-[_,_] {x} {y} {z})
                   (λ {x} {y} {z} → ≤-⊓₀ {x} {y} {z})
                   (λ {x} {y} {z} → ≤-⊓₁ {x} {y} {z})
                   (λ {x} {y} {z} → ≤-⊔₀ {x} {y} {z})
                   (λ {x} {y} {z} → ≤-⊔₁ {x} {y} {z})
    module FS = FunctionSorting _<=_
    module FSP = FS.Properties isTotalOrder
                   ≤-⊔ ⊓-≤
                   (λ {x} {y} {z} → ≤-<_,_> {x} {y} {z})
                   (λ {x} {y} {z} → ≤-[_,_] {x} {y} {z})
                   (λ {x} {y} {z} → ≤-⊓₀ {x} {y} {z})
                   (λ {x} {y} {z} → ≤-⊓₁ {x} {y} {z})
                   (λ {x} {y} {z} → ≤-⊔₀ {x} {y} {z})
                   (λ {x} {y} {z} → ≤-⊔₁ {x} {y} {z})
    open SortedData _≤_ isPreorder public
    open SortingBijSpec _<=_ isTotalOrder public
    open EvalTree public using (evalTree)
    open BijSpec public
    open import Data.Bits.OperationSyntax public
    open FS public using () renaming (sort to sortFun)

    merge : ∀ {n} → Tree (Bits m) (1 + n) → Tree (Bits m) (1 + n)
    merge = S.merge

    sort : ∀ {n} → Tree (Bits m) n → Tree (Bits m) n
    sort = S.sort

    merge-spec : ∀ {n} {t : Tree (Bits m) (1 + n)} → PreSorted t → Sorted (merge t)
    merge-spec = SP.merge-spec

    sort-spec : ∀ {n} (t : Tree (Bits m) n) → Sorted (sort t)
    sort-spec = SP.sort-spec

-- -}
-- -}
-- -}
-- -}

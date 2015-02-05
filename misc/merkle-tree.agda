module merkle-tree where

open import Data.One
open import Data.Vec
open import Data.List as L
open import Data.Nat.NP
open import Relation.Binary.PropositionalEquality.NP

module _ {A : Set} (_⊕_ : A → A → A) where
  zip/2 : ∀ {n} → Vec A n → Vec A ⌈ n /2⌉
  zip/2 [] = []
  zip/2 (x ∷ []) = x ∷ []
  zip/2 (x₀ ∷ x₁ ∷ xs) = (x₀ ⊕ x₁) ∷ zip/2 xs

{-# TERMINATING #-}
log2-1+ : ℕ → ℕ
log2-1+ zero    = zero
log2-1+ (suc n) = suc (log2-1+ ⌊ n /2⌋)

data Pos : (n : ℕ) → Set where
  pos : ∀ {n} → Pos (suc n)

log2 : (n : ℕ) .{{n>0 : Pos n}} → ℕ
log2 0 {{()}}
log2 (suc n) = log2-1+ n

2*′/2 : ∀ n → ⌊ 2*′ n /2⌋ ≡ n
2*′/2 zero = refl
2*′/2 (suc n) = cong suc (2*′/2 n)

2*/2 : ∀ n → ⌊ 2* n /2⌋ ≡ n
2*/2 n rewrite ! 2*′-spec n = 2*′/2 n

2*′>0 : ∀ {n} → Pos n → Pos (2*′ n)
2*′>0 pos = pos

2*>0 : ∀ {n} → Pos n → Pos (2* n)
2*>0 pos = pos

2^>0 : ∀ n → Pos (2^ n)
2^>0 0 = pos
2^>0 1 = pos
2^>0 (suc (suc n)) = 2*>0 {2^(suc n)} (2^>0 (suc n))

log2-2*′-1+ : ∀ n .{{n>0 : Pos n}} → log2 (2*′ n) {{2*′>0 n>0}} ≡ 1 + log2 n
log2-2*′-1+ 0 {{()}}
log2-2*′-1+ (suc n) rewrite 2*′/2 n = refl

log2-2*-1+ : ∀ n .{{n>0 : Pos n}} → log2 (2* n) {{2*>0 n>0}} ≡ 1 + log2 n
log2-2*-1+ zero {{()}}
log2-2*-1+ (suc n) rewrite ℕ°.+-comm n (suc n) | 2*/2 n = refl

log2-2^-id : ∀ n → log2 (2^ n) {{2^>0 n}} ≡ n
log2-2^-id 0       = refl
log2-2^-id (suc n) = log2-2*-1+ (2^ n) {{2^>0 n}} ∙ ap suc (log2-2^-id n)

-- log2-*-+ : log2 (m * n) ≡ log2 m + log2 n

module _ {A T : Set} (empty : T) (leaf : A → T) (fork : T → T → T) where
  private
    go : List T → List T
    go [] = []
    go (t ∷ []) = t ∷ []
    go (t₀ ∷ t₁ ∷ ts) = fork t₀ t₁ ∷ go ts

    {-# TERMINATING #-}
    og : List T → T
    og [] = empty
    og (t ∷ []) = t
    og (t₀ ∷ t₁ ∷ ts) = og (fork t₀ t₁ ∷ go ts)

  mkTree : List A → T
  mkTree xs = og (L.map leaf xs)

data Bin (A : Set) : Set where
  leaf : (x : A) → Bin A
  fork : (l r : Bin A) → Bin A

-- ZBin A ≅ List (𝟚 × A)
data ZBin (A : Set) : Set where
  top   : ZBin A
  forkₗ : (l : ZBin A) (r : A) → ZBin A
  forkᵣ : (l : A) (r : ZBin A) → ZBin A

data RBin {A₀ A₁ : Set} (Aᵣ : A₀ → A₁ → Set) :
          (t₀ : Bin A₀) (t₁ : Bin A₁) → Set where
  leaf : ∀ {x₀ x₁} (x : Aᵣ x₀ x₁)
         → RBin Aᵣ (leaf x₀) (leaf x₁)
  fork : ∀ {l₀ l₁} (l : RBin Aᵣ l₀ l₁)
           {r₀ r₁} (r : RBin Aᵣ r₀ r₁)
         → RBin Aᵣ (fork l₀ r₀) (fork l₁ r₁)

module Inclusion' {A₀ A₁ : Set} (R : A₀ → Bin A₁ → Set) where
    data _⊆_ : (t₀ : Bin A₀) (t₁ : Bin A₁) → Set where
      leaf : ∀ {x t} → R x t → leaf x ⊆ t
      fork : ∀ {l₀ l₁} (l : l₀ ⊆ l₁)
               {r₀ r₁} (r : r₀ ⊆ r₁)
             → fork l₀ r₀ ⊆ fork l₁ r₁

data Path : Set where
  [] : Path
  0∷_ 1∷_ : Path → Path

{-
pattern top = []
pattern left  p = 0∷ p
pattern right p = 1∷ p
-}

module Inclusion (Aside : ∀ {A} → Bin A → Set) where
    data _⊆_/_ {A : Set} : Bin A → Bin A → Path → Set where
      []  : ∀ {x} → x ⊆ x / []
      left : ∀ {p t₀ t₁ x}
            → x ⊆ t₀ / p
            → Aside t₁
            → x ⊆ (fork t₀ t₁)/ 0∷ p
      right : ∀ {p t₀ t₁ x}
            → Aside t₀
            → x ⊆ t₁ / p
            → x ⊆ (fork t₀ t₁)/ 1∷ p

    _∈_/_ : {A : Set} → A → Bin A → Path → Set
    x ∈ t / p = leaf x ⊆ t / p

record Triv {A : Set} (x : A) : Set where
  constructor triv

-- open Inclusion Triv

data Leaf {A : Set} : Bin A → Set where
  leaf : (x : A) → Leaf (leaf x)

module Min = Inclusion Leaf

-- Catamorphism for Bin, seen as computing hashes.
module H1 {D : Set} (h₂ : D → D → D) (RD : D → D → Set) where
  hBin : Bin D → D
  hBin (leaf d) = d
  hBin (fork t₀ t₁) = h₂ (hBin t₀) (hBin t₁)

  module M = Inclusion' {D} {D} (λ x t → x ≡ hBin t)

  open Inclusion' {𝟙} {D} (λ x t → 𝟙)

  {-
  prune : {t₀ t₁ : Bin D} → t₀ ⊆ t₁ → Bin D
  prune t [] [] = t
  prune (fork t₀ t₁) (1∷ p) (right x q) = fork (leaf (hBin t₀)) (prune t₁ p q)
  prune (fork t₀ t₁) (0∷ p) (left q x) = fork (prune t₀ p q) (leaf (hBin t₁))

  {-
  prune : (t : Bin D) (p : Path)
          {s : Bin D} (_ : s ⊆ t / p) → Bin D
  prune t [] [] = t
  prune (fork t₀ t₁) (1∷ p) (right x q) = fork (leaf (hBin t₀)) (prune t₁ p q)
  prune (fork t₀ t₁) (0∷ p) (left q x) = fork (prune t₀ p q) (leaf (hBin t₁))

-- Catamorphism for Bin, seen as computing hashes.
module H2 {A D : Set} (h₁ : A → D) (h₂ : D → D → D)
         (RD : D → D → Set) where
  hBin : Bin A → D
  hBin (leaf x) = h₁ x
  hBin (fork t₀ t₁) = h₂ (hBin t₀) (hBin t₁)

  _~_ : (t u : Bin A) → Set
  t ~ u = RD (hBin t) (hBin u)

  _⊑_ : (t u : Bin A) → Set
  t ⊑ u = {!x ∈ hBin t ≡ hBin u!}

  {-

data _⊆min_[_] {A : Set} : Bin A → Bin A → Path → Set where
  []  : ∀ {x} → x ⊆ x [ [] ]
  0∷_ : ∀ {p t₀ x₁ x}
        → x ⊆ t₀ [ p ]
        → x ⊆ (fork t₀ (leaf x₁))[ 0∷ p ]
  1∷_ : ∀ {p x₀ t₁ x}
        → x ⊆ t₁ [ p ]
        → x ⊆ (fork (leaf x₀) t₁)[ 1∷ p ]
data _∈_ {A : Set} : Path → Bin A → Set where
  []  : [] ∈ {!!}
  0∷_ : ∀ {p t₀ t₁} → p ∈ t₀ → 0∷ p ∈ fork t₀ t₁
  1∷_ : ∀ {p t₀ t₁} → p ∈ t₁ → 1∷ p ∈ fork t₀ t₁
-- -}
-- -}
-- -}
-- -}
-- -}

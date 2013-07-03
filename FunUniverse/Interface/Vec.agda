open import FunUniverse.Core
open import Data.Nat.NP
module FunUniverse.Interface.Vec
         {t} {T : Set t} (funU : FunUniverse T) where
open FunUniverse funU

record FunVec : Set where
  field
    tt→[]  : ∀ {A} → `⊤ `→ `Vec A 0
    []→tt  : ∀ {A} → `Vec A 0 `→ `⊤
    <∷>    : ∀ {n A} → (A `× `Vec A n) `→ `Vec A (1 + n)
    uncons : ∀ {n A} → `Vec A (1 + n) `→ (A `× `Vec A n)

    fst<,[]> : ∀ {A B} → A `× `Vec B 0 `→ A
    snd<[],> : ∀ {A B} → `Vec A 0 `× B `→ B
    <_∷′_> : ∀ {n A B C} → (A `→ C) → (B `→ `Vec C n)
                        → A `× B `→ `Vec C (1 + n)
    <_∷_> : ∀ {m n A B} → (A `→ B) → (`Vec A m `→ `Vec B n)
                    → `Vec A (1 + m) `→ `Vec B (1 + n)

    <tt⁏_∷′_> : ∀ {n A B} → (`⊤ `→ B) → (A `→ `Vec B n)
                        → A `→ `Vec B (1 + n)

    <_∷′tt⁏_> : ∀ {n A B} → (A `→ B) → (`⊤ `→ `Vec B n)
                          → A `→ `Vec B (1 + n)

    <_∷[]> : ∀ {A B} → (A `→ B) → A `→ `Vec B 1

    <∷[]> : ∀ {A} → A `→ `Vec A 1

    <[],_> : ∀ {A B C} → (A `→ B) → A `→ `Vec C 0 `× B

    <_,[]> : ∀ {A B C} → (A `→ B) → A `→ B `× `Vec C 0

    head<∷> : ∀ {A} → `Vec A 1 `→ A

    constVec⊤ : ∀ {n a} {A : Set a} {B} → (A → `⊤ `→ B) → Vec A n → `⊤ `→ `Vec B n

    []→[] : ∀ {A B} → `Vec A 0 `→ `Vec B 0

    <[],[]>→[] : ∀ {A B C} → (`Vec A 0 `× `Vec B 0) `→ `Vec C 0

    <_⊛> : ∀ {n A B} → Vec (A `→ B) n → `Vec A n `→ `Vec B n

    foldl : ∀ {n A B} → (B `× A `→ B) → (B `× `Vec A n) `→ B

    foldl₁ : ∀ {n A} → (A `× A `→ A) → `Vec A (1 + n) `→ A

    foldr : ∀ {n A B} → (A `× B `→ B) → (`Vec A n `× B) `→ B

    foldr₁ : ∀ {n A} → (A `× A `→ A) → `Vec A (1 + n) `→ A

    map : ∀ {n A B} → (A `→ B) → (`Vec A n `→ `Vec B n)

    zipWith : ∀ {n A B C} → ((A `× B) `→ C)
                          → (`Vec A n `× `Vec B n) `→ `Vec C n

    zip : ∀ {n A B} → (`Vec A n `× `Vec B n) `→ `Vec (A `× B) n

    snoc : ∀ {n A} → (`Vec A n `× A) `→ `Vec A (1 + n)

    reverse : ∀ {n A} → `Vec A n `→ `Vec A n

    append : ∀ {m n A} → (`Vec A m `× `Vec A n) `→ `Vec A (m + n)

    <_++_> : ∀ {m n A} → (`⊤ `→ `Vec A m) → (`⊤ `→ `Vec A n) →
                          `⊤ `→ `Vec A (m + n)

    splitAt : ∀ m {n A} → `Vec A (m + n) `→ (`Vec A m `× `Vec A n)

    rot-left : ∀ m {n A} → `Vec A (m + n) `→ `Vec A (n + m)

    rot-right : ∀ {m} n {A} → `Vec A (m + n) `→ `Vec A (n + m)

    folda : ∀ n {A} → (A `× A `→ A) → `Vec A (2^ n) `→ A

    concat : ∀ {m n A} → `Vec (`Vec A m) n `→ `Vec A (n * m)

    group : ∀ {A} n k → `Vec A (n * k) `→ `Vec (`Vec A k) n

    bind : ∀ {m n A B} → (A `→ `Vec B m) → `Vec A n `→ `Vec B (n * m)

    replicate⊤ : ∀ n → `⊤ `→ `Vec `⊤ n

    -- Vectors
    <[]> : ∀ {_⊤ A} → _⊤ `→ `Vec A 0
    -- * <∷> and uncons come from LinRewiring

    head : ∀ {n A} → `Vec A (1 + n) `→ A

    tail : ∀ {n A} → `Vec A (1 + n) `→ `Vec A n

    constVec : ∀ {n a _⊤} {A : Set a} {B} → (A → `⊤ `→ B) → Vec A n → _⊤ `→ `Vec B n

    take : ∀ m {n A} → `Vec A (m + n) `→ `Vec A m

    drop : ∀ m {n A} → `Vec A (m + n) `→ `Vec A n

    msb : ∀ m {n} → (m + n) `→ᵇ m

    lsb : ∀ {n} k → (n + k) `→ᵇ k

    init : ∀ {n A} → `Vec A (1 + n) `→ `Vec A n

    last : ∀ {n A} → `Vec A (1 + n) `→ A

    replicate : ∀ {n A} → A `→ `Vec A n

    constBits′ : ∀ {n A} → Bits n → (A `× A) `→ `Vec A n

    -- Notice that this one costs 1 unit of space.
    dup⁏<_∷′_> : ∀ {n A B} → (A `→ B) → (A `→ `Vec B n)
                          → A `→ `Vec B (1 + n)

    allBits : ∀ n → `⊤ `→ `Vec (`Bits n) (2^ n)

    lookupTbl : ∀ {n A} → `Bits n `× `Vec A (2^ n) `→ A

    funFromTbl : ∀ {n A} → Vec (`⊤ `→ A) (2^ n) → (`Bits n `→ A)

    tblFromFun : ∀ {n A} → (`Bits n `→ A) → `⊤ `→ `Vec A (2^ n)

-- -}

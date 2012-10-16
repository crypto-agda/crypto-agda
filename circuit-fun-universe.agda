open import Data.Nat  using (ℕ; _+_)
open import Data.Bits using (Bits)
open import Data.Fin  using (Fin)

open import data-universe

module circuit-fun-universe where

infix 0 _⌥_
data _⌥_ : ℕ → ℕ → Set where
  rewire : ∀ {i o} → (Fin o → Fin i) → i ⌥ o
    -- cost: 0 time, o space
  _∘_    : ∀ {m n o} → (n ⌥ o) → (m ⌥ n) → (m ⌥ o)
    -- cost: sum time and space
  <_×_>  : ∀ {m n o p} → (m ⌥ o) → (n ⌥ p) → (m + n) ⌥ (o + p)
    -- cost: max time and sum space
  cond   : ∀ {n} → (1 + (n + n)) ⌥ n
    -- cost: 1 time, 1 space
  bits   : ∀ {n _⊤} → Bits n → _⊤ ⌥ n
    -- cost: 0 time, n space
  xor    : ∀ {n} → Bits n → n ⌥ n
    -- cost: 1 time, n space

  {- derived rewiring
  id        : ∀ {A} → A `→ A
  dup       : ∀ {A} → A `→ A `× A
  fst       : ∀ {A B} → A `× B `→ A
  snd       : ∀ {A B} → A `× B `→ B
  swap      : ∀ {A B} → (A `× B) `→ (B `× A)
  assoc     : ∀ {A B C} → ((A `× B) `× C) `→ (A `× (B `× C))
  tt        : ∀ {_⊤} → _⊤ `→ `⊤
  <[]>      : ∀ {_⊤ A} → _⊤ `→ `Vec A 0
  <∷>       : ∀ {n A} → (A `× `Vec A n) `→ `Vec A (1 + n)
  uncons    : ∀ {n A} → `Vec A (1 + n) `→ (A `× `Vec A n)
  <tt,id>   : ∀ {A} → A `→ `⊤ `× A
  snd<tt,>  : ∀ {A} → `⊤ `× A `→ A
  tt→[]     : ∀ {A} → `⊤ `→ `Vec A 0
  []→tt     : ∀ {A} → `Vec A 0 `→ `⊤
  rewireTbl : ∀ {i o} → RewireTbl i o   → `Bits i `→ `Bits o
  -}
  {- derived from <_×_> and id:
  first     : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B)
  second    : ∀ {A B C} → (B `→ C) → (A `× B) `→ (A `× C)
  -}
  {- derived from <_×_> and dup:
  <_,_>     : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  -}
  {- derived from cond:
  bijFork   : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ `Bit `× B
  fork      : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B
  -}
  {- derived from bits
  <0b> <1b> : ∀ {_⊤} → _⊤ `→ `Bit
  -}

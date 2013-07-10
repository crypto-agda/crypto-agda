{-# OPTIONS --without-K #-}
module md5 where

open import Type
open import Data.Fin using (Fin)
open import Data.Bits using (Bits)
open import Data.Nat

infix 0 _⌥_
infixr 1 _⁏_
infix 0 _`→_
_`×_ = _+_
`Bit = 1
`Bits : ℕ → ℕ
`Bits n = n
postulate
  -- ℕ : Set
  _⊞_ : ∀ {q} → Fin q → Fin q → Fin q
  _⌥_ : ℕ → ℕ → ★

_`→_ = _⌥_
postulate
  rewire : ∀ {i o} → (Fin o → Fin i) → i ⌥ o
    -- cost: 0 time, o space
  _∘_    : ∀ {m n o} → (n ⌥ o) → (m ⌥ n) → (m ⌥ o)
  _⁏_    : ∀ {m n o} → (m ⌥ n) → (n ⌥ o) → (m ⌥ o)
  dup : ∀ {n} → n ⌥ (n + n)
    -- cost: sum time and space
  <_×_>  : ∀ {m n o p} → (m ⌥ o) → (n ⌥ p) → (m + n) ⌥ (o + p)
    -- cost: max time and sum space
  cond   : ∀ {n} → (1 + (n + n)) ⌥ n
    -- cost: 1 time, 1 space
  bits   : ∀ {n _⊤} → Bits n → _⊤ ⌥ n
    -- cost: 0 time, n space
  --xor    : ∀ {n} → Bits n → n ⌥ n
    -- cost: 1 time, n space
  id        : ∀ {A} → A `→ A
  fst       : ∀ {A B} → A `× B `→ A
  snd       : ∀ {A B} → A `× B `→ B
  swap      : ∀ {A B} → (A `× B) `→ (B `× A)
  assoc     : ∀ {A B C} → ((A `× B) `× C) `→ (A `× (B `× C))
  {-
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
  first     : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B)
  second    : ∀ {A B C} → (B `→ C) → (A `× B) `→ (A `× C)
  <_,_>     : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  bijFork   : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ `Bit `× B
  fork      : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B
  <0b> <1b> : ∀ {_⊤} → _⊤ `→ `Bit
  xor : ∀ {n} → (n + n) ⌥ n
  and : ∀ {n} → (n + n) ⌥ n
  or  : ∀ {n} → (n + n) ⌥ n
  add : ∀ {A} → (A + A) `→ A
  neg : ∀ {n} → n ⌥ n

record Proj A B : Set where
  field
    get : A `→ B
    on  : (A `× B) `→ B → A `→ A
open Proj

module Ops
  (F G : ℕ → ★)
  (lift₁ : ∀ {A B} → A `→ B → F A → G B)
  (lift₂ : ∀ {A B C} → (A `× B) `→ C → F A → F B → G C) where

    infixl 6 _`+_ _⊕_
    _`+_ : ∀ {A} → F A → F A → G A
    _`+_ = lift₂ add

    _⊕_ : ∀ {A} → F A → F A → G A
    _⊕_ = lift₂ xor

    _∧_ : ∀ {A} → F A → F A → G A
    _∧_ = lift₂ and

    _∨_ : ∀ {A} → F A → F A → G A
    _∨_ = lift₂ or

    ¬_ : ∀ {A} → F A → G A
    ¬_ = lift₁ neg

rol : ∀ {n} → Fin n → n `→ n
rol x = rewire (_⊞_ x)

_+=_ : ∀ {A B} → Proj A B → A `→ B → A `→ A
p += c = on p (first c ⁏ add)

module SOps
  (F : ℕ → ★)
  (lift₁ : ∀ {A B} → A `→ B → F A → F B)
  (lift₂ : ∀ {A B C} → (A `× B) `→ C → F A → F B → F C)
  where

    open Ops F F lift₁ lift₂ public

    Op3 : ℕ → ★
    Op3 A = F A → F A → F A → F A

    R : ∀ {A B : ℕ} {I : ★} → (I → A `→ B) → Op3 B → (a b c d : Proj A B) (i : I) (k : Bits B) (s : Fin B) → _
    R {A} {B} w f a b c d i k s =
      a += ({!f (get b) (get c) (get d) {- `+ w i `+ bits k -}!}) ⁏ on a (snd {A} ⁏ rol s) ⁏ a += get b

    module f1,2,3,4 (A : ℕ) where

        f1 : Op3 A
        f2 : Op3 A
        f3 : Op3 A
        f4 : Op3 A

        f1 x y z = z ⊕ (x ∧ (y ⊕ z))
        f2 x y z = f1 z x y -- y ⊕ (z ∧ (x ⊕ y))
        f3 x y z = x ⊕ y ⊕ z
        f4 x y z = y ⊕ (x ∨ ¬ z)

    {-
lift₁ : ∀ {A B C} → B `→ C → Proj A B → A `→ C
lift₁ op p = get p ⁏ op

lift₂ : ∀ {A B C D} → (B `× C) `→ D → Proj A B → Proj A C → A `→ D
lift₂ op p₀ p₁ = dup ⁏ < get p₀ × get p₁ > ⁏ op

module Ops' {A} = Ops (Proj A) (_`→_ A) lift₁ lift₂
open Ops'
-}

lift₁ : ∀ {A B C} → B `→ C → A `→ B → A `→ C
lift₁ op p = p ⁏ op

lift₂ : ∀ {A B C D} → (B `× C) `→ D → A `→ B → A `→ C → A `→ D
lift₂ op p₀ p₁ = dup ⁏ < p₀ × p₁ > ⁏ op

module SOps' {A} = SOps (_`→_ A) lift₁ lift₂
-- open SOps'

{-
x : ∀ {A B} → (A `× B) `→ A
x = fst
y : ∀ {A B C} → (A `× B `× C) `→ B
y = snd ⁏ fst
z : ∀ {A B C D} → (A `× B `× C `× D) `→ C
z = snd ⁏ snd ⁏ fst
-}

{-
partofmd5 =
  R f1 a b c d 0 0xd76aa478 7  ⁏
  R f1 d a b c 1 0xe8c7b756 12 ⁏
  R f1 c d a b 2 0x242070db 17 ⁏
  R f1 b c d a 3 0xc1bdceee 22
  -- -}
  -- -}
  -- -}
  -- -}
  -- -}

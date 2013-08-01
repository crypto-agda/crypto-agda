{-# OPTIONS --without-K #-}
open import Type
open import Data.Nat
open import Data.Bit using (Bit)
open import Data.Bits using (Bits; RewireTbl)
open import Data.Fin using (Fin)
open import FunUniverse.Data
open import FunUniverse.Core
open import FunUniverse.Category
open import FunUniverse.Rewiring.Linear

module FunUniverse.Syntax {T : ★} (dataU : Universe T) where

open Universe dataU

infix 0 _`→_
data _`→_ : T → T → ★ where
    id        : ∀ {A} → A `→ A
    _∘_       : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C)

    fst       : ∀ {A B} → A `× B `→ A
    snd       : ∀ {A B} → A `× B `→ B
    first     : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B)
    second    : ∀ {A B C} → (B `→ C) → (A `× B) `→ (A `× C)
    swap      : ∀ {A B} → (A `× B) `→ (B `× A)
    assoc     : ∀ {A B C} → ((A `× B) `× C) `→ (A `× (B `× C))
    <_×_>     : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
    <_,_>     : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
    dup       : ∀ {A} → A `→ A `× A

    tt        : ∀ {_𝟙} → _𝟙 `→ `𝟙

    <[]>      : ∀ {_𝟙 A} → _𝟙 `→ `Vec A 0
    <∷>       : ∀ {n A} → (A `× `Vec A n) `→ `Vec A (1 + n)
    uncons    : ∀ {n A} → `Vec A (1 + n) `→ (A `× `Vec A n)

    bijFork   : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ `Bit `× B
    cond      : ∀ {A} → `Bit `× A `× A `→ A
    fork      : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B

    <0b> <1b> : ∀ {_𝟙} → _𝟙 `→ `Bit

    xor       : ∀ {n} → Bits n → `Bits n `→ `Bits n
    rewire    : ∀ {i o} → (Fin o → Fin i) → `Bits i `→ `Bits o
    rewireTbl : ∀ {i o} → RewireTbl i o   → `Bits i `→ `Bits o

    <tt,id>   : ∀ {A} → A `→ `𝟙 `× A
    snd<tt,>  : ∀ {A} → `𝟙 `× A `→ A
    tt→[]     : ∀ {A} → `𝟙 `→ `Vec A 0
    []→tt     : ∀ {A} → `Vec A 0 `→ `𝟙

synU : FunUniverse T
synU = dataU , _`→_

synCat : Category _`→_
synCat = id , _∘_

synLin : LinRewiring synU
synLin = mk synCat first swap assoc <tt,id> snd<tt,> <_×_>
            second tt→[] []→tt <∷> uncons

synRewiring : Rewiring synU
synRewiring = mk synLin tt dup <[]> <_,_> fst snd rewire rewireTbl

synFork : HasFork synU
synFork = cond , fork

synOps : FunOps synU
synOps = mk synRewiring synFork <0b> <1b>

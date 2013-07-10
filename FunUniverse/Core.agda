{-# OPTIONS --without-K #-}
module FunUniverse.Core where

open import Type
open import Data.Nat.NP using (ℕ; zero; suc; _+_; _*_; 2^_)
import Data.Bool.NP as B
open B using (if_then_else_; true; false)
open import Data.Unit using (⊤)
open import Data.Fin using (Fin)
open import Function using (_∘′_; flip)
import Data.Vec.NP as V
import Level as L
open V using (Vec; []; _∷_)

open import Data.Bit using (Bit; 0b; 1b)
open import Data.Bits using (Bits; _→ᵇ_; RewireTbl; 0ⁿ; 1ⁿ)

import FunUniverse.BinTree as Tree
open Tree using (Tree)
open import FunUniverse.Data

open import FunUniverse.Types public
import FunUniverse.Defaults.FirstPart as Defaults⟨first-part⟩
open import FunUniverse.Rewiring.Linear

record HasBijFork {t} {T : Set t} (funU : FunUniverse T) : Set t where
  constructor mk
  open FunUniverse funU
  field
    -- bijFork f₀ f₁ (0₂ , x) = 0₂ , f₀ x
    -- bijFork f₀ f₁ (1₂ , x) = 1₂ , f₁ x
    bijFork : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ `Bit `× B

  -- bijFork′ f₀ f₁ (0₂ , x) = 0₂ , f₀ 0₂ x
  -- bijFork′ f₀ f₁ (1₂ , x) = 1₂ , f₁ 1₂ x
  bijFork′ : ∀ {A B} → (Bit → A `→ B) → `Bit `× A `→ `Bit `× B
  bijFork′ f = bijFork (f 0b) (f 1b)

record HasFork {t} {T : Set t} (funU : FunUniverse T) : Set t where
  constructor _,_
  open FunUniverse funU
  field
    -- cond (0₂ , x₀ , x₁) = x₀
    -- cond (1₂ , x₀ , x₁) = x₁
    -- See Defaults.DefaultCond
    cond : ∀ {A} → `Bit `× A `× A `→ A

    -- fork f₀ f₁ (0₂ , x) = f₀ x
    -- fork f₀ f₁ (1₂ , x) = f₁ x
    -- See Defaults.DefaultFork
    fork : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B

  fork′ : ∀ {A B} → (Bit → A `→ B) → `Bit `× A `→ B
  fork′ f = fork (f 0b) (f 1b)

record HasXor {t} {T : Set t} (funU : FunUniverse T) : Set t where
  constructor mk
  open FunUniverse funU
  field
    xor : ∀ {n} → Bits n → `Endo (`Bits n)

  vnot : ∀ {n} → `Endo (`Bits n)
  vnot = xor 1ⁿ

  ⟨⊕_⟩ : ∀ {n} → Bits n → `Endo (`Bits n)
  ⟨⊕ xs ⟩ = xor xs

record Bijective {t} {T : Set t} (funU : FunUniverse T) : Set t where
  constructor mk

  field
    linRewiring : LinRewiring funU
    hasBijFork  : HasBijFork  funU
    hasXor      : HasXor      funU

record Rewiring {t} {T : Set t} (funU : FunUniverse T) : Set t where
  constructor mk
  open FunUniverse funU

  field
    linRewiring : LinRewiring funU

    -- Unit (ignoring its argument)
    tt : ∀ {_⊤} → _⊤ `→ `𝟙

    -- Products (all that comes from LinRewiring)
    dup : ∀ {A} → A `→ A `× A

    -- Vectors
    <[]> : ∀ {_⊤ A} → _⊤ `→ `Vec A 0
    -- * <∷> and uncons come from LinRewiring

    -- Products (group 1 primitive functions or derived from group 2)
    <_,_> : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
    fst   : ∀ {A B} → A `× B `→ A
    snd   : ∀ {A B} → A `× B `→ B

    rewire    : ∀ {i o} → (Fin o → Fin i) → i `→ᵇ o
    rewireTbl : ∀ {i o} → RewireTbl i o    → i `→ᵇ o

  open LinRewiring linRewiring public

  proj : ∀ {A} → Bit → (A `× A) `→ A
  proj true  = fst
  proj false = snd

  head : ∀ {n A} → `Vec A (1 + n) `→ A
  head = uncons ⁏ fst

  tail : ∀ {n A} → `Vec A (1 + n) `→ `Vec A n
  tail = uncons ⁏ snd

  constVec : ∀ {n a _⊤} {A : Set a} {B} → (A → `𝟙→ B) → Vec A n → _⊤ `→ `Vec B n
  constVec f vec = tt ⁏ constVec⊤ f vec

  take : ∀ m {n A} → `Vec A (m + n) `→ `Vec A m
  take zero    = <[]>
  take (suc m) = < id ∷ take m >

  drop : ∀ m {n A} → `Vec A (m + n) `→ `Vec A n
  drop zero    = id
  drop (suc m) = tail ⁏ drop m

  msb : ∀ m {n} → (m + n) `→ᵇ m
  msb m = take m

  lsb : ∀ {n} k → (n + k) `→ᵇ k
  lsb {n} _ = drop n

  init : ∀ {n A} → `Vec A (1 + n) `→ `Vec A n
  init {zero}  = <[]>
  init {suc n} = < id ∷ init >

  last : ∀ {n A} → `Vec A (1 + n) `→ A
  last {zero}  = head
  last {suc n} = tail ⁏ last

  replicate : ∀ {n A} → A `→ `Vec A n
  replicate {zero}  = <[]>
  replicate {suc n} = < id , replicate > ⁏ <∷>

  constBits′ : ∀ {n A} → Bits n → (A `× A) `→ `Vec A n
  constBits′ [] = <[]>
  constBits′ (b ∷ xs) = dup ⁏ < proj b ∷′ constBits′ xs >

record FunOps {t} {T : Set t} (funU : FunUniverse T) : Set t where
  constructor mk
  open FunUniverse funU

  field
    rewiring : Rewiring funU
    hasFork  : HasFork  funU

    -- Bit
    <0b> <1b> : ∀ {_⊤} → _⊤ `→ `Bit

    -- Products
    -- * <_×_>; first; second; swap; assoc; <tt,id>; snd<tt,> come from LinRewiring
    -- * dup; <_,_>; fst; snd come from Rewiring

    -- Vectors
    -- <[]>; <∷>; uncons come from Rewiring

  open Defaults⟨first-part⟩ funU
  open Rewiring rewiring public
  open HasFork  hasFork  public

  -- Bad idea™
  <if_then_else_> : ∀ {A B} (b : A `→ `Bit) (f g : A `→ B) → A `→ B
  <if b then if-1 else if-0 > = < b , id > ⁏ fork if-0 if-1

  not : `Bit `→ `Bit
  not = <id,tt> ⁏ fork <1b> <0b>

  -- We might want it to be part of the interface
  hasXor : HasXor funU
  hasXor = mk (DefaultXor.xor id not <_⊛>)

  hasBijFork : HasBijFork funU
  hasBijFork = mk (DefaultBijForkFromFork.bijFork <_,_> fst fork)

  bijective : Bijective funU
  bijective = mk linRewiring hasBijFork hasXor

  open HasXor     hasXor public
  open HasBijFork hasBijFork public

  infixr 3 _&&&_
  _&&&_ : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  f &&& g = < f , g >

  constBit : ∀ {_⊤} → Bit → _⊤ `→ `Bit
  constBit b = if b then <1b> else <0b>

  -- Notice that this one costs 1 unit of space.
  dup⁏<_∷′_> : ∀ {n A B} → (A `→ B) → (A `→ `Vec B n)
                         → A `→ `Vec B (1 + n)
  dup⁏< f ∷′ g > = dup ⁏ < f ∷′ g >

  <0,_> : ∀ {A B} → (A `→ B) → A `→ `Bit `× B
  <0, f > = <tt⁏ <0b> , f >

  <1,_> : ∀ {A B} → (A `→ B) → A `→ `Bit `× B
  <1, f > = <tt⁏ <1b> , f >

  <0,> : ∀ {A} → A `→ `Bit `× A
  <0,> = <0, id >

  <1,> : ∀ {A} → A `→ `Bit `× A
  <1,> = <1, id >

  <0,1> : ∀ {_⊤} → _⊤ `→ `Bit `× `Bit
  <0,1> = <0, <1b> >

  <0∷_> : ∀ {n A} → (A `→ `Bits n) → A `→ `Bits (1 + n)
  <0∷ f > = <tt⁏ <0b> ∷′ f >

  <1∷_> : ∀ {n A} → (A `→ `Bits n) → A `→ `Bits (1 + n)
  <1∷ f > = <tt⁏ <1b> ∷′ f >

  <0∷> : ∀ {n} → n `→ᵇ (1 + n)
  <0∷> = <0∷ id >

  <1∷> : ∀ {n} → n `→ᵇ (1 + n)
  <1∷> = <1∷ id >

  constBits : ∀ {n _⊤} → Bits n → _⊤ `→ `Bits n
  constBits = constVec constBit

  <0ⁿ> : ∀ {n _⊤} → _⊤ `→ `Bits n
  <0ⁿ> = constBits 0ⁿ

  <1ⁿ> : ∀ {n _⊤} → _⊤ `→ `Bits n
  <1ⁿ> = constBits 1ⁿ

  constBits′′ : ∀ {n _⊤} → Bits n → _⊤ `→ `Bits n
  constBits′′ bs = <0,1> ⁏ constBits′ bs

  `Maybe : T → T
  `Maybe A = `Bit `× A

  <nothing> : ∀ {A} → A `→ `Maybe A
  <nothing> = <0,>

  <just> : ∀ {A} → A `→ `Maybe A
  <just> = <1,>

  <is-just?_∶_> : ∀ {A B C} → (f : A `× B `→ C) (g : B `→ C) → `Maybe A `× B `→ C
  <is-just? f ∶ g > = <if fst ⁏ fst then first snd ⁏ f else snd ⁏ g >

  _∣?_ : ∀ {A} → `Maybe A `× `Maybe A `→ `Maybe A
  _∣?_ = <is-just? fst ⁏ <just> ∶ id >

  _`→?_ : T → T → Set
  A `→? B = A `→ `Maybe B

  search : ∀ {n A} → (A `× A `→ A) → (`Bits n `→ A) → `𝟙→ A
  search {zero}  _  f = <[]> ⁏ f
  search {suc n} op f = <tt⁏ search op (f ∘ <0∷>) , search op (f ∘ <1∷>) > ⁏ op

  find? : ∀ {n A} → (`Bits n `→? A) → `𝟙 `→? A
  find? = search _∣?_

  findB : ∀ {n} → (`Bits n `→ `Bit) → `𝟙 `→? `Bits n
  findB pred = find? <if pred then <just> else <nothing> >

  fromTree : ∀ {n A} → Tree (`𝟙 `→ A) n → `Bits n `→ A
  fromTree (Tree.leaf x) = tt ⁏ x
  fromTree (Tree.fork t₀ t₁) = uncons ⁏ fork (fromTree t₀) (fromTree t₁)

  fromFun : ∀ {n A} → (Bits n → `𝟙→ A) → `Bits n `→ A
  fromFun = fromTree ∘′ Tree.fromFun

  fromBitsFun : ∀ {i o} → (i →ᵇ o) → i `→ᵇ o
  fromBitsFun f = fromFun (constBits ∘′ f)

  <xor> : `Bit `× `Bit `→ `Bit
  <xor> = fork id not

  <or> : `Bit `× `Bit `→ `Bit
  <or> = fork id <1b>

  <and> : `Bit `× `Bit `→ `Bit
  <and> = fork <0b> id

  <==ᵇ> : `Bit `× `Bit `→ `Bit
  <==ᵇ> = <xor> ⁏ not

  <==> : ∀ {n} → `Bits n `× `Bits n `→ `Bit
  <==> {zero}  = <1b>
  <==> {suc n} = < uncons × uncons > ⁏ < <==ᵇ> `zip` <==> {n} > ⁏ <or>

  <⊕> : ∀ {n} → `Bits n `× `Bits n `→ `Bits n
  <⊕> = zipWith <xor>

  -- vnot : ∀ {n} → `Endo (`Bits n)
  -- vnot = map not

  allBits : ∀ n → `𝟙→ `Vec (`Bits n) (2^ n)
  allBits zero    = < <[]> ∷[]>
  allBits (suc n) = < bs ⁏ map <0∷> ++ bs ⁏ map <1∷> >
    where bs = allBits n

  sucBCarry : ∀ {n} → `Bits n `→ `Bits (1 + n)
  sucBCarry {zero}  = < <0b> ∷[]>
  sucBCarry {suc n} = uncons
                    ⁏ fork <0∷ sucBCarry >
                          (sucBCarry ⁏ uncons ⁏ fork <0∷ <1∷> > <1∷ <0∷> >)

  sucB : ∀ {n} → `Bits n `→ `Bits n
  sucB = sucBCarry ⁏ tail

  half-adder : `Bit `× `Bit `→ `Bit `× `Bit
  half-adder = < <xor> , <and> >

  -- full-adder (Cᵢₙ , A , B) = (Cₒᵤₜ , S)
  full-adder : `Bit `× `Bit `× `Bit `→ `Bit `× `Bit
  full-adder = < cout , s >
    where a    = snd ⁏ fst
          b    = snd ⁏ snd
          cin  = fst
          s    = second <xor> ⁏ <xor>
          cout = <   < a , b > ⁏ <and>
                 , < < a , b > ⁏ <xor> , cin > ⁏ <and> >
               ⁏ <or> -- this one can also be a <xor>

  {-
  full-adder = < (sc₂ ⁏ fst) , < (sc₁ ⁏ snd) , (sc₂ ⁏ snd) > ⁏ <or> >
    where a   = snd ⁏ fst
          b   = snd ⁏ snd
          cᵢₙ = fst
          sc₁ = < a , b > ⁏ half-adder
          sc₂ = < (sc₁ ⁏ fst) , cᵢₙ > ⁏ half-adder
  -}

  lookupTbl : ∀ {n A} → `Bits n `× `Vec A (2^ n) `→ A
  lookupTbl {zero} = snd ⁏ head
  lookupTbl {suc n}
    = first uncons
    ⁏ assoc
    ⁏ fork (second (take (2^ n)) ⁏ lookupTbl)
           (second (drop (2^ n)) ⁏ lookupTbl)

  funFromTbl : ∀ {n A} → Vec (`𝟙→ A) (2^ n) → (`Bits n `→ A)
  funFromTbl {zero} (x ∷ []) = tt ⁏ x
  funFromTbl {suc n} tbl
    = uncons ⁏ fork (funFromTbl (V.take (2^ n) tbl))
                    (funFromTbl (V.drop (2^ n) tbl))

  tblFromFun : ∀ {n A} → (`Bits n `→ A) → `𝟙→ `Vec A (2^ n)
  tblFromFun {zero}  f = < <[]> ⁏ f ∷[]>
  tblFromFun {suc n} f = < tblFromFun (<0∷> ⁏ f) ++
                           tblFromFun (<1∷> ⁏ f) >

  module WithFin
    (`Fin : ℕ → T)
    (fz : ∀ {n _⊤} → _⊤ `→ `Fin (suc n))
    (fs : ∀ {n} → `Fin n `→ `Fin (suc n))
    (elim-Fin0 : ∀ {A} → `Fin 0 `→ A)
    (elim-Fin1+ : ∀ {n A B} → (A `→ B) → (`Fin n `× A `→ B) → `Fin (suc n) `× A `→ B) where

    tabulate : ∀ {n A _B} → (`Fin n `→ A) → _B `→ `Vec A n
    tabulate {zero}  f = <[]>
    tabulate {suc n} f = <tt⁏ fz ⁏ f ∷′ tabulate (fs ⁏ f) >

    lookup : ∀ {n A} → `Fin n `× `Vec A n `→ A
    lookup {zero}  = fst ⁏ elim-Fin0
    lookup {suc n} = elim-Fin1+ head (second tail ⁏ lookup)

    allFin : ∀ {n _⊤} → _⊤ `→ `Vec (`Fin n) n
    allFin = tabulate id

module Defaults {t} {T : Set t} (funU : FunUniverse T) where
  open FunUniverse funU
  open Defaults⟨first-part⟩ funU public

  module RewiringDefaults
    (linRewiring : LinRewiring funU)
    (tt       : ∀ {_⊤} → _⊤ `→𝟙)
    (dup      : ∀ {A} → A `→ A `× A)
    (rewire   : ∀ {i o} → (Fin o → Fin i) → i `→ᵇ o) where

    open LinRewiring linRewiring
    open DefaultsGroup1 _∘_ tt snd<tt,> dup swap first public
    <[]> : ∀ {_⊤ A} → _⊤ `→ `Vec A 0
    <[]> = tt ⁏ tt→[]
    open DefaultRewireTbl rewire public
-- -}

module flat-funs where

open import Data.Nat.NP using (ℕ; zero; suc; _+_; _*_; 2^_)
open import Data.Bool using (if_then_else_)
open import Function using (_∘′_)
import Data.Vec.NP as V
import Level as L
open V using (Vec; []; _∷_)

open import Data.Bits using (Bit; Bits)

import bintree as Tree
open Tree using (Tree)
open import data-universe

record FlatFuns {t} (T : Set t) : Set (L.suc t) where
  constructor mk
  field
    universe : Universe T
    _`→_    : T → T → Set
  infix 0 _`→_
  open Universe universe public

module Defaults {t} {T : Set t} (♭Funs : FlatFuns T) where
  open FlatFuns ♭Funs

  module CompositionNotations
    (_∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C)) where

    infixr 1 _⁏_
    infixr 1 _>>>_

    _⁏_ : ∀ {a b c} → (a `→ b) → (b `→ c) → (a `→ c)
    f ⁏ g = g ∘ f

    _>>>_ : ∀ {a b c} → (a `→ b) → (b `→ c) → (a `→ c)
    f >>> g = f ⁏ g

  module DefaultsFirstSecond
    (id : ∀ {A} → A `→ A)
    (<_×_> : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)) where

    first : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B)
    first f = < f × id >

    second : ∀ {A B C} → (B `→ C) → (A `× B) `→ (A `× C)
    second f = < id × f >

  module DefaultsGroup2
    (id : ∀ {A} → A `→ A)
    (_∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C))
    (tt : ∀ {_A} → _A `→ `⊤)
    (<_,_> : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C)
    (fst   : ∀ {A B} → A `× B `→ A)
    (snd   : ∀ {A B} → A `× B `→ B) where

    <_×_> : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
    < f × g > = < f ∘ fst , g ∘ snd >

    open DefaultsFirstSecond id <_×_> public

    dup : ∀ {A} → A `→ A `× A
    dup = < id , id >

    swap : ∀ {A B} → (A `× B) `→ (B `× A)
    swap = < snd , fst >

    assoc : ∀ {A B C} → ((A `× B) `× C) `→ (A `× (B `× C))
    assoc = < fst ∘ fst , first snd >

    <tt,id> : ∀ {A} → A `→ `⊤ `× A
    <tt,id> = < tt , id >

    snd<tt,> : ∀ {A} → `⊤ `× A `→ A
    snd<tt,> = snd

  module DefaultsGroup1
    (id : ∀ {A} → A `→ A)
    (_∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C))
    (tt : ∀ {_A} → _A `→ `⊤)
    (snd<tt,> : ∀ {A} → `⊤ `× A `→ A)
    (dup   : ∀ {A} → A `→ A `× A)
    (swap  : ∀ {A B} → (A `× B) `→ (B `× A))
    (first : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B)) where

    open CompositionNotations _∘_

    second : ∀ {A B C} → (B `→ C) → (A `× B) `→ (A `× C)
    second f = swap ⁏ first f ⁏ swap

    <_×_> : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
    < f × g > = first f ⁏ second g

    <_,_> : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
    < f , g > = dup ⁏ < f × g >

    snd : ∀ {A B} → A `× B `→ B
    snd = first tt ⁏ snd<tt,>

    fst : ∀ {A B} → A `× B `→ A
    fst = swap ⁏ snd

  module <×>Default
    (_∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C))
    (first : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B))
    (swap  : ∀ {A B} → (A `× B) `→ (B `× A))
    where
    open CompositionNotations _∘_

    <_×_> : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
    < f × g > = first f ⁏ swap ⁏ first g ⁏ swap

  module DefaultAssoc′
    (_∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C))
    (assoc : ∀ {A B C} → ((A `× B) `× C) `→ (A `× (B `× C)))
    (swap  : ∀ {A B} → (A `× B) `→ (B `× A))
    (first : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B))
    where
    open CompositionNotations _∘_

    -- This definition would cost 1 unit of space instead of 0.
    -- assoc′ : ∀ {A B C} → (A `× (B `× C)) `→ ((A `× B) `× C)
    -- assoc′ = < second fst , snd ⁏ snd >

    assoc′ : ∀ {A B C} → (A `× (B `× C)) `→ ((A `× B) `× C)
    assoc′ = swap ⁏ first swap ⁏ assoc ⁏ swap ⁏ first swap

  module DefaultCond
    (fork : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B)
    (fst   : ∀ {A B} → A `× B `→ A)
    (snd   : ∀ {A B} → A `× B `→ B) where

    cond : ∀ {A} → `Bit `× A `× A `→ A
    cond = fork fst snd

   -- This definition cost 2 units of space instead of 1.
  module DefaultFork
    (_∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C))
    (second : ∀ {A B C} → (B `→ C) → (A `× B) `→ (A `× C))
    (<_,_> : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C)
    (cond : ∀ {A} → `Bit `× A `× A `→ A) where

    open CompositionNotations _∘_

    fork : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B
    fork f g = second < f , g > ⁏ cond

record FlatFunsOps {t} {T : Set t} (♭Funs : FlatFuns T) : Set t where
  constructor mk
  open FlatFuns ♭Funs

  infixr 9 _∘_
  infixr 3 _***_
  infixr 3 _&&&_
  field
    -- Functions
    id : ∀ {A} → A `→ A
    _∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C)

    -- Bit
    <0b> <1b> : ∀ {_A} → _A `→ `Bit
    cond      : ∀ {A} → `Bit `× A `× A `→ A
    fork      : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B

    -- Unit
    tt : ∀ {_A} → _A `→ `⊤

    -- Products (group 1 primitive functions or derived from group 2)
    <_,_> : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
    fst   : ∀ {A B} → A `× B `→ A
    snd   : ∀ {A B} → A `× B `→ B

    -- Products (group 2 primitive functions or derived from group 1)
    dup      : ∀ {A} → A `→ A `× A
    first    : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B)
    swap     : ∀ {A B} → (A `× B) `→ (B `× A)
    assoc    : ∀ {A B C} → ((A `× B) `× C) `→ (A `× (B `× C))
    <tt,id>  : ∀ {A} → A `→ `⊤ `× A
    snd<tt,> : ∀ {A} → `⊤ `× A `→ A

    -- Products (derived from group 1 or 2)
    <_×_>  : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
    second : ∀ {A B C} → (B `→ C) → (A `× B) `→ (A `× C)

    -- Vectors
    nil    : ∀ {_A B} → _A `→ `Vec B 0
    cons   : ∀ {n A} → (A `× `Vec A n) `→ `Vec A (1 + n)
    uncons : ∀ {n A} → `Vec A (1 + n) `→ (A `× `Vec A n)

  open Defaults ♭Funs
  open CompositionNotations _∘_ public

  _&&&_ : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  f &&& g = < f , g >

  _***_ : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
  f *** g = < f × g >

  constBit : ∀ {_A} → Bit → _A `→ `Bit
  constBit b = if b then <1b> else <0b>

  <tt⁏_,_> : ∀ {A B C} → (`⊤ `→ B) → (A `→ C) → A `→ B `× C
  <tt⁏ f , g > = <tt,id> ⁏ < f × g >

  <_,tt⁏_> : ∀ {A B C} → (A `→ B) → (`⊤ `→ C) → A `→ B `× C
  < f ,tt⁏ g > = <tt⁏ g , f > ⁏ swap

  open DefaultAssoc′ _∘_ assoc swap first public

  <if_then_else_> : ∀ {A B} (b : A `→ `Bit) (f g : A `→ B) → A `→ B
  <if b then if-1 else if-0 > = < b , id > ⁏ fork if-0 if-1

  assoc-first : ∀ {A B C D E} → (A `× B `→ D `× E) → A `× B `× C `→ D `× E `× C
  assoc-first f = assoc′ ⁏ first f ⁏ assoc

  assoc-second : ∀ {A B C D E} → (B `× C `→ E `× D) → (A `× B) `× C `→ (A `× E) `× D
  assoc-second f = assoc ⁏ second f ⁏ assoc′

  <_`zip`_> : ∀ {A B C D E F} → ((A `× B) `→ C)
                           → ((D `× E) `→ F)
                           → ((A `× D) `× (B `× E)) `→ (C `× F)
  < f `zip` g > = assoc-first (assoc-second swap) ⁏ < f × g >

{- This one use one unit of space
  < f `zip` g > = < < fst × fst > ⁏ f ,
                    < snd × snd > ⁏ g >
-}

  head : ∀ {n A} → `Vec A (1 + n) `→ A
  head = uncons ⁏ fst

  tail : ∀ {n A} → `Vec A (1 + n) `→ `Vec A n
  tail = uncons ⁏ snd

  <_∷_> : ∀ {m n A B} → (A `→ B) → (`Vec A m `→ `Vec B n)
                  → `Vec A (1 + m) `→ `Vec B (1 + n)
  < f ∷ g > = uncons ⁏ < f × g > ⁏ cons

  <_∷′_> : ∀ {n A B C} → (A `→ C) → (B `→ `Vec C n)
                       → A `× B `→ `Vec C (1 + n)
  < f ∷′ g > = < f × g > ⁏ cons

  -- Notice that this one costs 1 unit of space.
  dup⁏<_∷′_> : ∀ {n A B} → (A `→ B) → (A `→ `Vec B n)
                         → A `→ `Vec B (1 + n)
  dup⁏< f ∷′ g > = dup ⁏ < f ∷′ g >

  <tt⁏_∷′_> : ∀ {n A B} → (`⊤ `→ B) → (A `→ `Vec B n)
                       → A `→ `Vec B (1 + n)
  <tt⁏ f ∷′ g > = <tt⁏ f , g > ⁏ cons

  <_∷′tt⁏_> : ∀ {n A B} → (A `→ B) → (`⊤ `→ `Vec B n)
                        → A `→ `Vec B (1 + n)
  < f ∷′tt⁏ g > = < f ,tt⁏ g > ⁏ cons

  <0,_> : ∀ {A B} → (A `→ B) → A `→ `Bit `× B
  <0, f > = <tt⁏ <0b> , f >

  <1,_> : ∀ {A B} → (A `→ B) → A `→ `Bit `× B
  <1, f > = <tt⁏ <1b> , f >

  <0,> : ∀ {A} → A `→ `Bit `× A
  <0,> = <0, id >

  <1,> : ∀ {A} → A `→ `Bit `× A
  <1,> = <1, id >

  <0∷_> : ∀ {n A} → (A `→ `Bits n) → A `→ `Bits (1 + n)
  <0∷ f > = <tt⁏ <0b> ∷′ f >

  <1∷_> : ∀ {n A} → (A `→ `Bits n) → A `→ `Bits (1 + n)
  <1∷ f > = <tt⁏ <1b> ∷′ f >

  <0∷> : ∀ {n} → `Bits n `→ `Bits (1 + n)
  <0∷> = <0∷ id >

  <1∷> : ∀ {n} → `Bits n `→ `Bits (1 + n)
  <1∷> = <1∷ id >

  constVec : ∀ {n b _A} {B : Set b} {C} → (B → `⊤ `→ C) → Vec B n → _A `→ `Vec C n
  constVec f [] = nil
  constVec f (x ∷ xs) = <tt⁏ f x ∷′ constVec f xs >

  constBits : ∀ {n _A} → Bits n → _A `→ `Bits n
  constBits = constVec constBit

  foldl : ∀ {n A B} → (B `× A `→ B) → (B `× `Vec A n) `→ B
  foldl {zero}  f = fst
  foldl {suc n} f = second uncons
                  ⁏ assoc′
                  ⁏ first f
                  ⁏ foldl f

  foldl₁ : ∀ {n A} → (A `× A `→ A) → `Vec A (1 + n) `→ A
  foldl₁ f = uncons ⁏ foldl f

  foldr : ∀ {n A B} → (A `× B `→ B) → (`Vec A n `× B) `→ B
  foldr {zero}  f = snd
  foldr {suc n} f = first uncons
                  ⁏ assoc
                  ⁏ second (foldr f)
                  ⁏ f

  foldr₁ : ∀ {n A} → (A `× A `→ A) → `Vec A (1 + n) `→ A
  foldr₁ f = uncons ⁏ swap ⁏ foldr f

  <_⊛> : ∀ {n A B} → Vec (A `→ B) n → `Vec A n `→ `Vec B n
  <_⊛> []       = nil
  <_⊛> (f ∷ fs) = < f ∷ < fs ⊛> >

  map : ∀ {n A B} → (A `→ B) → (`Vec A n `→ `Vec B n)
  map f = < V.replicate f ⊛>

  zipWith : ∀ {n A B C} → ((A `× B) `→ C)
                        → (`Vec A n `× `Vec B n) `→ `Vec C n
  zipWith {zero}  f = nil
  zipWith {suc n} f = < uncons × uncons >
                    ⁏ < f `zip` (zipWith f) >
                    ⁏ cons

  zip : ∀ {n A B} → (`Vec A n `× `Vec B n) `→ `Vec (A `× B) n
  zip = zipWith id

  <nil,_> : ∀ {A B C} → (A `→ B) → A `→ `Vec C 0 `× B
  <nil, f > = <tt⁏ nil , f >

  <_,nil> : ∀ {A B C} → (A `→ B) → A `→ B `× `Vec C 0
  < f ,nil> = < f ,tt⁏ nil >

  singleton : ∀ {A} → A `→ `Vec A 1
  singleton = < id ,nil> ⁏ cons

  snoc : ∀ {n A} → (`Vec A n `× A) `→ `Vec A (1 + n)
  snoc {zero}  = snd ⁏ singleton
  snoc {suc n} = first uncons ⁏ assoc ⁏ second snoc ⁏ cons

  reverse : ∀ {n A} → `Vec A n `→ `Vec A n
  reverse {zero}  = nil
  reverse {suc n} = uncons ⁏ swap ⁏ first reverse ⁏ snoc

  append : ∀ {m n A} → (`Vec A m `× `Vec A n) `→ `Vec A (m + n)
  append {zero}  = snd
  append {suc m} = first uncons
                 ⁏ assoc
                 ⁏ second append
                 ⁏ cons

  splitAt : ∀ m {n A} → `Vec A (m + n) `→ (`Vec A m `× `Vec A n)
  splitAt zero    = <nil, id >
  splitAt (suc m) = uncons
                  ⁏ second (splitAt m)
                  ⁏ assoc′
                  ⁏ first cons

  take : ∀ m {n A} → `Vec A (m + n) `→ `Vec A m
  take zero    = nil
  take (suc m) = < id ∷ take m >

  drop : ∀ m {n A} → `Vec A (m + n) `→ `Vec A n
  drop zero    = id
  drop (suc m) = tail ⁏ drop m

  folda : ∀ n {A} → (A `× A `→ A) → `Vec A (2^ n) `→ A
  folda zero    f = head
  folda (suc n) f = splitAt (2^ n) ⁏ < folda n f × folda n f > ⁏ f

  init : ∀ {n A} → `Vec A (1 + n) `→ `Vec A n
  init {zero}  = nil
  init {suc n} = < id ∷ init >

  last : ∀ {n A} → `Vec A (1 + n) `→ A
  last {zero}  = head
  last {suc n} = tail ⁏ last

  concat : ∀ {m n A} → `Vec (`Vec A m) n `→ `Vec A (n * m)
  concat {n = zero}  = nil
  concat {n = suc n} = uncons ⁏ second concat ⁏ append

  group : ∀ {A} n k → `Vec A (n * k) `→ `Vec (`Vec A k) n
  group zero    k = nil
  group (suc n) k = splitAt k ⁏ second (group n k) ⁏ cons

  bind : ∀ {m n A B} → (A `→ `Vec B m) → `Vec A n `→ `Vec B (n * m)
  bind f = map f ⁏ concat

  replicate : ∀ {n A} → A `→ `Vec A n
  replicate {zero}  = nil
  replicate {suc n} = < id , replicate > ⁏ cons

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

  search : ∀ {n A} → (A `× A `→ A) → (`Bits n `→ A) → `⊤ `→ A
  search {zero}  _  f = nil ⁏ f
  search {suc n} op f = <tt⁏ search op (f ∘ <0∷>) , search op (f ∘ <1∷>) > ⁏ op

  find? : ∀ {n A} → (`Bits n `→? A) → `⊤ `→? A
  find? = search _∣?_

  findB : ∀ {n} → (`Bits n `→ `Bit) → `⊤ `→? `Bits n
  findB pred = find? <if pred then <just> else <nothing> >

  fromTree : ∀ {n A} → Tree (`⊤ `→ A) n → `Bits n `→ A
  fromTree (Tree.leaf x) = tt ⁏ x
  fromTree (Tree.fork t₀ t₁) = uncons ⁏ fork (fromTree t₀) (fromTree t₁)

  fromFun : ∀ {n A} → (Bits n → `⊤ `→ A) → `Bits n `→ A
  fromFun = fromTree ∘′ Tree.fromFun

  fromBitsFun : ∀ {i o} → (Bits i → Bits o) → `Bits i `→ `Bits o
  fromBitsFun f = fromFun (constBits ∘′ f)

  module WithFin
    (`Fin : ℕ → T)
    (fz : ∀ {n _A} → _A `→ `Fin (suc n))
    (fs : ∀ {n} → `Fin n `→ `Fin (suc n))
    (elim-Fin0 : ∀ {A} → `Fin 0 `→ A)
    (elim-Fin1+ : ∀ {n A B} → (A `→ B) → (`Fin n `× A `→ B) → `Fin (suc n) `× A `→ B) where

    tabulate : ∀ {n A _B} → (`Fin n `→ A) → _B `→ `Vec A n
    tabulate {zero}  f = nil
    tabulate {suc n} f = <tt⁏ fz ⁏ f , tabulate (fs ⁏ f) > ⁏ cons

    lookup : ∀ {n A} → `Fin n `× `Vec A n `→ A
    lookup {zero}  = fst ⁏ elim-Fin0
    lookup {suc n} = elim-Fin1+ head (second tail ⁏ lookup)

    allFin : ∀ {n _A} → _A `→ `Vec (`Fin n) n
    allFin = tabulate id

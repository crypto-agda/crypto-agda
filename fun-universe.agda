module fun-universe where

open import Data.Nat.NP using (ℕ; zero; suc; _+_; _*_; 2^_)
open import Data.Bool using (if_then_else_; true; false)
open import Data.Unit using (⊤)
open import Data.Fin using (Fin)
open import Function using (_∘′_; flip)
import Data.Vec.NP as V
import Level as L
open V using (Vec; []; _∷_)

open import Data.Bits using (Bit; Bits; _→ᵇ_; RewireTbl; 0ⁿ; 1ⁿ)

import bintree as Tree
open Tree using (Tree)
open import data-universe

record FunUniverse {t} (T : Set t) : Set (L.suc t) where
  constructor mk
  field
    universe : Universe T
    _`→_    : T → T → Set

  infix 0 _`→_
  open Universe universe public

  _`→ᵇ_ : ℕ → ℕ → Set
  i `→ᵇ o = `Bits i `→ `Bits o

  `Endo : T → Set
  `Endo A = A `→ A

module Defaults⟨first-part⟩ {t} {T : Set t} (funU : FunUniverse T) where
  open FunUniverse funU

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
    (tt : ∀ {_⊤} → _⊤ `→ `⊤)
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

  module DefaultSecondFromFirstSwap
    (_∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C))
    (first : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B))
    (swap  : ∀ {A B} → (A `× B) `→ (B `× A)) where

    open CompositionNotations _∘_

    second : ∀ {A B C} → (B `→ C) → (A `× B) `→ (A `× C)
    second f = swap ⁏ first f ⁏ swap

  module Default<×>FromFirstSecond
    (_∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C))
    (first : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B))
    (second : ∀ {A B C} → (B `→ C) → (A `× B) `→ (A `× C)) where

    open CompositionNotations _∘_

    <_×_> : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
    < f × g > = first f ⁏ second g

  module DefaultFstFromSndSwap
    (_∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C))
    (snd : ∀ {A B} → A `× B `→ B)
    (swap  : ∀ {A B} → (A `× B) `→ (B `× A)) where

    open CompositionNotations _∘_

    fst : ∀ {A B} → A `× B `→ A
    fst = swap ⁏ snd

  module DefaultsGroup1
    (_∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C))
    (tt : ∀ {_⊤} → _⊤ `→ `⊤)
    (snd<tt,> : ∀ {A} → `⊤ `× A `→ A)
    (dup   : ∀ {A} → A `→ A `× A)
    (swap  : ∀ {A B} → (A `× B) `→ (B `× A))
    (first : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B)) where

    open CompositionNotations _∘_
    open DefaultSecondFromFirstSwap _∘_ first swap public
    open Default<×>FromFirstSecond _∘_ first second public

    <_,_> : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
    < f , g > = dup ⁏ < f × g >

    snd : ∀ {A B} → A `× B `→ B
    snd = first tt ⁏ snd<tt,>

    open DefaultFstFromSndSwap _∘_ snd swap public

  module <×>Default
    (_∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C))
    (first : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B))
    (swap  : ∀ {A B} → (A `× B) `→ (B `× A)) where

    open CompositionNotations _∘_

    <_×_> : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
    < f × g > = first f ⁏ swap ⁏ first g ⁏ swap

  module DefaultAssoc
    (_∘_   : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C))
    (<_,_> : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C)
    (fst   : ∀ {A B} → A `× B `→ A)
    (snd   : ∀ {A B} → A `× B `→ B) where

    open CompositionNotations _∘_

    assoc : ∀ {A B C} → ((A `× B) `× C) `→ (A `× (B `× C))
    assoc = < fst ⁏ fst , < fst ⁏ snd , snd > >

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

  module DefaultRewire
    (rewireTbl : ∀ {i o} → RewireTbl i o → i `→ᵇ o) where

    rewire : ∀ {i o} → (Fin o → Fin i) → i `→ᵇ o
    rewire fun = rewireTbl (V.tabulate fun)

  module DefaultRewireTbl
    (rewire : ∀ {i o} → (Fin o → Fin i) → i `→ᵇ o) where

    rewireTbl : ∀ {i o} → RewireTbl i o → i `→ᵇ o
    rewireTbl tbl = rewire (flip V.lookup tbl)

  module LinDefaults
    (_∘_   : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C))
    (first : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B))
    (swap  : ∀ {A B} → (A `× B) `→ (B `× A))
    (assoc : ∀ {A B C} → ((A `× B) `× C) `→ (A `× (B `× C))) where

    open CompositionNotations _∘_ public
    open <×>Default _∘_ first swap public
    open DefaultSecondFromFirstSwap _∘_ first swap public
    open DefaultAssoc′ _∘_ assoc swap first public

record LinRewiring {t} {T : Set t} (funU : FunUniverse T) : Set t where
  constructor mk
  open FunUniverse funU

  infixr 9 _∘_
  field
    -- Functions
    id : ∀ {A} → A `→ A
    _∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C)

    -- Products (group 2 primitive functions or derived from group 1)
    first    : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B)
    swap     : ∀ {A B} → (A `× B) `→ (B `× A)
    assoc    : ∀ {A B C} → ((A `× B) `× C) `→ (A `× (B `× C))
    <tt,id>  : ∀ {A} → A `→ `⊤ `× A
    snd<tt,> : ∀ {A} → `⊤ `× A `→ A

    -- Products (derived from group 1 or 2)
    <_×_>  : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
    second : ∀ {A B C} → (B `→ C) → (A `× B) `→ (A `× C)

    -- Vectors
    tt→[] : ∀ {A} → `⊤ `→ `Vec A 0
    []→tt : ∀ {A} → `Vec A 0 `→ `⊤
    <∷>    : ∀ {n A} → (A `× `Vec A n) `→ `Vec A (1 + n)
    uncons  : ∀ {n A} → `Vec A (1 + n) `→ (A `× `Vec A n)

  open Defaults⟨first-part⟩ funU
  open CompositionNotations _∘_ public
  open DefaultAssoc′ _∘_ assoc swap first public

  infixr 3 _***_
  _***_ : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
  f *** g = < f × g >

  <tt⁏_,_> : ∀ {A B C} → (`⊤ `→ B) → (A `→ C) → A `→ B `× C
  <tt⁏ f , g > = <tt,id> ⁏ < f × g >

  <_,tt⁏_> : ∀ {A B C} → (A `→ B) → (`⊤ `→ C) → A `→ B `× C
  < f ,tt⁏ g > = <tt⁏ g , f > ⁏ swap

  fst<,tt> : ∀ {A} → A `× `⊤ `→ A
  fst<,tt> = swap ⁏ snd<tt,>

  fst<,[]> : ∀ {A B} → A `× `Vec B 0 `→ A
  fst<,[]> = second []→tt ⁏ fst<,tt>

  snd<[],> : ∀ {A B} → `Vec A 0 `× B `→ B
  snd<[],> = first []→tt ⁏ snd<tt,>

  -- Like first, but applies on a triple associated the other way
  assoc-first : ∀ {A B C D E} → (A `× B `→ D `× E) → A `× B `× C `→ D `× E `× C
  assoc-first f = assoc′ ⁏ first f ⁏ assoc

  swap-top : ∀ {A B C} → A `× B `× C `→ B `× A `× C
  swap-top = assoc-first swap

  -- Like assoc-first but for second
  assoc-second : ∀ {A B C D E} → (B `× C `→ E `× D) → (A `× B) `× C `→ (A `× E) `× D
  assoc-second f = assoc ⁏ second f ⁏ assoc′

  <_×₁_> : ∀ {A B C D E F} → (A `× B `→ D `× E) → (C `→ F) → A `× B `× C `→ D `× E `× F
  < f ×₁ g > = assoc′ ⁏ < f × g > ⁏ assoc

  <_×₂_> : ∀ {A B C D E F} → (A `→ D) → (B `× C `→ E `× F) → (A `× B) `× C `→ (D `× E) `× F
  < f ×₂ g > = assoc ⁏ < f × g > ⁏ assoc′

  <_`zip`_> : ∀ {A B C D E F} → ((A `× B) `→ C)
                           → ((D `× E) `→ F)
                           → ((A `× D) `× (B `× E)) `→ (C `× F)
  < f `zip` g > = assoc-first (assoc-second swap) ⁏ < f × g >

{- This one use one unit of space
  < f `zip` g > = < < fst × fst > ⁏ f ,
                    < snd × snd > ⁏ g >
-}

  <_∷′_> : ∀ {n A B C} → (A `→ C) → (B `→ `Vec C n)
                       → A `× B `→ `Vec C (1 + n)
  < f ∷′ g > = < f × g > ⁏ <∷>

  <_∷_> : ∀ {m n A B} → (A `→ B) → (`Vec A m `→ `Vec B n)
                  → `Vec A (1 + m) `→ `Vec B (1 + n)
  < f ∷ g > = uncons ⁏ < f ∷′ g >

  <tt⁏_∷′_> : ∀ {n A B} → (`⊤ `→ B) → (A `→ `Vec B n)
                       → A `→ `Vec B (1 + n)
  <tt⁏ f ∷′ g > = <tt⁏ f , g > ⁏ <∷>

  <_∷′tt⁏_> : ∀ {n A B} → (A `→ B) → (`⊤ `→ `Vec B n)
                        → A `→ `Vec B (1 + n)
  < f ∷′tt⁏ g > = < f ,tt⁏ g > ⁏ <∷>

  <_∷[]> : ∀ {A B} → (A `→ B) → A `→ `Vec B 1
  < f ∷[]> = < f ∷′tt⁏ tt→[] >

  <∷[]> : ∀ {A} → A `→ `Vec A 1
  <∷[]> = < id ∷[]>

  <[],_> : ∀ {A B C} → (A `→ B) → A `→ `Vec C 0 `× B
  <[], f > = <tt⁏ tt→[] , f >

  <_,[]> : ∀ {A B C} → (A `→ B) → A `→ B `× `Vec C 0
  < f ,[]> = < f ,tt⁏ tt→[] >

  head<∷> : ∀ {A} → `Vec A 1 `→ A
  head<∷> = uncons ⁏ fst<,[]>

  constVec⊤ : ∀ {n a} {A : Set a} {B} → (A → `⊤ `→ B) → Vec A n → `⊤ `→ `Vec B n
  constVec⊤ f [] = tt→[]
  constVec⊤ f (x ∷ xs) = <tt⁏ f x ∷′ constVec⊤ f xs >

  []→[] : ∀ {A B} → `Vec A 0 `→ `Vec B 0
  []→[] = []→tt ⁏ tt→[]

  <[],[]>→[] : ∀ {A B C} → (`Vec A 0 `× `Vec B 0) `→ `Vec C 0
  <[],[]>→[] = fst<,[]> ⁏ []→[]

  <_⊛> : ∀ {n A B} → Vec (A `→ B) n → `Vec A n `→ `Vec B n
  <_⊛> []       = []→[]
  <_⊛> (f ∷ fs) = < f ∷ < fs ⊛> >

  foldl : ∀ {n A B} → (B `× A `→ B) → (B `× `Vec A n) `→ B
  foldl {zero}  f = fst<,[]>
  foldl {suc n} f = second uncons
                  ⁏ assoc′
                  ⁏ first f
                  ⁏ foldl f

  foldl₁ : ∀ {n A} → (A `× A `→ A) → `Vec A (1 + n) `→ A
  foldl₁ f = uncons ⁏ foldl f

  foldr : ∀ {n A B} → (A `× B `→ B) → (`Vec A n `× B) `→ B
  foldr {zero}  f = snd<[],>
  foldr {suc n} f = first uncons
                  ⁏ assoc
                  ⁏ second (foldr f)
                  ⁏ f

  foldr₁ : ∀ {n A} → (A `× A `→ A) → `Vec A (1 + n) `→ A
  foldr₁ f = uncons ⁏ swap ⁏ foldr f

  map : ∀ {n A B} → (A `→ B) → (`Vec A n `→ `Vec B n)
  map f = < V.replicate f ⊛>

  zipWith : ∀ {n A B C} → ((A `× B) `→ C)
                        → (`Vec A n `× `Vec B n) `→ `Vec C n
  zipWith {zero}  f = <[],[]>→[]
  zipWith {suc n} f = < uncons × uncons >
                    ⁏ < f `zip` (zipWith f) >
                    ⁏ <∷>

  zip : ∀ {n A B} → (`Vec A n `× `Vec B n) `→ `Vec (A `× B) n
  zip = zipWith id

  snoc : ∀ {n A} → (`Vec A n `× A) `→ `Vec A (1 + n)
  snoc {zero}  = < snd<[],> ∷[]>
  snoc {suc n} = first uncons ⁏ assoc ⁏ second snoc ⁏ <∷>

  reverse : ∀ {n A} → `Vec A n `→ `Vec A n
  reverse {zero}  = id
  reverse {suc n} = uncons ⁏ swap ⁏ first reverse ⁏ snoc

  append : ∀ {m n A} → (`Vec A m `× `Vec A n) `→ `Vec A (m + n)
  append {zero}  = snd<[],>
  append {suc m} = first uncons
                 ⁏ assoc
                 ⁏ second append
                 ⁏ <∷>

  <_++_> : ∀ {m n A} → (`⊤ `→ `Vec A m) → (`⊤ `→ `Vec A n) →
                         `⊤ `→ `Vec A (m + n)
  < f ++ g > = <tt⁏ f , g > ⁏ append

  splitAt : ∀ m {n A} → `Vec A (m + n) `→ (`Vec A m `× `Vec A n)
  splitAt zero    = <[], id >
  splitAt (suc m) = uncons
                  ⁏ second (splitAt m)
                  ⁏ assoc′
                  ⁏ first <∷>

  folda : ∀ n {A} → (A `× A `→ A) → `Vec A (2^ n) `→ A
  folda zero    f = head<∷>
  folda (suc n) f = splitAt (2^ n) ⁏ < folda n f × folda n f > ⁏ f

  concat : ∀ {m n A} → `Vec (`Vec A m) n `→ `Vec A (n * m)
  concat {n = zero}  = []→[]
  concat {n = suc n} = uncons ⁏ second concat ⁏ append

  group : ∀ {A} n k → `Vec A (n * k) `→ `Vec (`Vec A k) n
  group zero    k = []→[]
  group (suc n) k = splitAt k ⁏ second (group n k) ⁏ <∷>

  bind : ∀ {m n A B} → (A `→ `Vec B m) → `Vec A n `→ `Vec B (n * m)
  bind f = map f ⁏ concat

  replicate⊤ : ∀ n → `⊤ `→ `Vec `⊤ n
  replicate⊤ _ = constVec⊤ (λ _ → id) (V.replicate {A = ⊤} _)

  loop : ∀ {A} → ℕ → (A `→ A) → (A `→ A)
  loop zero    _ = id
  loop (suc n) f = f ⁏ loop n f
  -- or based on fold:
  -- loop n f = < id ,tt⁏ replicate⊤ n > ⁏ foldl (fst<,tt> ⁏ f)

record Rewiring {t} {T : Set t} (funU : FunUniverse T) : Set t where
  constructor mk
  open FunUniverse funU

  field
    linRewiring : LinRewiring funU

    -- Unit
    tt : ∀ {_⊤} → _⊤ `→ `⊤

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

  constVec : ∀ {n a _⊤} {A : Set a} {B} → (A → `⊤ `→ B) → Vec A n → _⊤ `→ `Vec B n
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

  -- this is problematic if the space cost is 1 unit
  constBits′ : ∀ {n A} → Bits n → (A `× A) `→ `Vec A n
  constBits′ [] = <[]>
  constBits′ (b ∷ xs) = dup ⁏ < proj b ∷′ constBits′ xs >

record FunOps {t} {T : Set t} (funU : FunUniverse T) : Set t where
  constructor mk
  open FunUniverse funU

  field
    rewiring : Rewiring funU

    -- Bit
    <0b> <1b> : ∀ {_⊤} → _⊤ `→ `Bit
    cond      : ∀ {A} → `Bit `× A `× A `→ A
    fork      : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B

    -- Products
    -- * <_×_>; first; second; swap; assoc; <tt,id>; snd<tt,> come from LinRewiring
    -- * dup; <_,_>; fst; snd come from Rewiring

    -- Vectors
    -- <[]>; <∷>; uncons come from Rewiring

  open Defaults⟨first-part⟩ funU
  open Rewiring rewiring public

  infixr 3 _&&&_
  _&&&_ : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  f &&& g = < f , g >

  constBit : ∀ {_⊤} → Bit → _⊤ `→ `Bit
  constBit b = if b then <1b> else <0b>

  <if_then_else_> : ∀ {A B} (b : A `→ `Bit) (f g : A `→ B) → A `→ B
  <if b then if-1 else if-0 > = < b , id > ⁏ fork if-0 if-1

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

  -- this is problematic if the space cost is 1 unit
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

  search : ∀ {n A} → (A `× A `→ A) → (`Bits n `→ A) → `⊤ `→ A
  search {zero}  _  f = <[]> ⁏ f
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

  fromBitsFun : ∀ {i o} → (i →ᵇ o) → i `→ᵇ o
  fromBitsFun f = fromFun (constBits ∘′ f)

  not : `Bit `→ `Bit
  not = <if id then <0b> else <1b> >

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

  vnot : ∀ {n} → `Endo (`Bits n)
  vnot = map not

  allBits : ∀ n → `⊤ `→ `Vec (`Bits n) (2^ n)
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

  lookupTbl : ∀ {n A} → `Bits n `× `Vec A (2^ n) `→ A
  lookupTbl {zero} = snd ⁏ head
  lookupTbl {suc n}
    = first uncons
    ⁏ assoc
    ⁏ fork (second (take (2^ n)) ⁏ lookupTbl)
           (second (drop (2^ n)) ⁏ lookupTbl)

  funFromTbl : ∀ {n A} → Vec (`⊤ `→ A) (2^ n) → (`Bits n `→ A)
  funFromTbl {zero} (x ∷ []) = tt ⁏ x
  funFromTbl {suc n} tbl
    = uncons ⁏ fork (funFromTbl (V.take (2^ n) tbl))
                    (funFromTbl (V.drop (2^ n) tbl))

  tblFromFun : ∀ {n A} → (`Bits n `→ A) → `⊤ `→ `Vec A (2^ n)
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
    (tt       : ∀ {_⊤} → _⊤ `→ `⊤)
    (dup      : ∀ {A} → A `→ A `× A)
    (rewire   : ∀ {i o} → (Fin o → Fin i) → i `→ᵇ o) where

    open LinRewiring linRewiring
    open DefaultsGroup1 _∘_ tt snd<tt,> dup swap first public
    <[]> : ∀ {_⊤ A} → _⊤ `→ `Vec A 0
    <[]> = tt ⁏ tt→[]
    open DefaultRewireTbl rewire public

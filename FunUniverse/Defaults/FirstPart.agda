open import FunUniverse.Types
import Data.Vec as V
open V using (Vec)
open import Data.Fin using (Fin)
open import Data.Bits using (Bits; RewireTbl)
import Data.Bool.NP as B
open import Function
import FunUniverse.Category

module FunUniverse.Defaults.FirstPart {t} {T : Set t} (funU : FunUniverse T) where
  open FunUniverse funU
  open FunUniverse.Category _`→_

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

  module DefaultCondFromFork
    (fork : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B)
    (fst  : ∀ {A B} → A `× B `→ A)
    (snd  : ∀ {A B} → A `× B `→ B) where

    cond : ∀ {A} → `Bit `× A `× A `→ A
    cond = fork fst snd

   -- This definition cost 2 units of space instead of 1.
  module DefaultForkFromCond
    (_∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C))
    (second : ∀ {A B C} → (B `→ C) → (A `× B) `→ (A `× C))
    (<_,_> : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C)
    (cond : ∀ {A} → `Bit `× A `× A `→ A) where

    open CompositionNotations _∘_

    fork : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B
    fork f g = second < f , g > ⁏ cond

  module DefaultForkFromBijFork
    (_∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C))
    (bijFork : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ `Bit `× B)
    (snd  : ∀ {A B} → A `× B `→ B) where

    open CompositionNotations _∘_

    fork : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B
    fork f g = bijFork f g ⁏ snd

  module DefaultBijForkFromCond
    (_∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C))
    (second : ∀ {A B C} → (B `→ C) → (A `× B) `→ (A `× C))
    (<_,_> : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C)
    (fst  : ∀ {A B} → A `× B `→ A)
    (cond : ∀ {A} → `Bit `× A `× A `→ A) where

    open CompositionNotations _∘_

    bijFork : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ `Bit `× B
    bijFork f g = second < f , g > ⁏ < fst , cond >

  module DefaultBijForkFromFork
    (<_,_> : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C)
    (fst  : ∀ {A B} → A `× B `→ A)
    (fork : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B) where

    bijFork : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ `Bit `× B
    bijFork f g = < fst , fork f g >

  module DefaultXor
     (id  : ∀ {A} → A `→ A)
     (not : `Bit `→ `Bit)
     (<_⊛> : ∀ {n A B} → Vec (A `→ B) n → `Vec A n `→ `Vec B n) where

    xor : ∀ {n} → Bits n → `Endo (`Bits n)
    xor xs = < V.map (B.cond not id) xs ⊛>

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

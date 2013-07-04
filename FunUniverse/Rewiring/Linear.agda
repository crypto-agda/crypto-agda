open import Level.NP
open import Type
open import FunUniverse.Types
open import Data.One using (𝟙)
import Data.Vec as V
open V using (Vec; []; _∷_)
open import Data.Nat.NP using (ℕ; zero; suc; _+_; _*_; 2^_)
import FunUniverse.Category
import FunUniverse.Defaults.FirstPart as Defaults⟨first-part⟩

module FunUniverse.Rewiring.Linear where

record LinRewiring {t} {T : ★_ t} (funU : FunUniverse T) : ★_ t where
  constructor mk
  open FunUniverse funU
  open FunUniverse.Category _`→_

  field
    cat : Category
  open Category cat

  field
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
    tt→[]  : ∀ {A} → `⊤ `→ `Vec A 0
    []→tt  : ∀ {A} → `Vec A 0 `→ `⊤
    <∷>    : ∀ {n A} → (A `× `Vec A n) `→ `Vec A (1 + n)
    uncons : ∀ {n A} → `Vec A (1 + n) `→ (A `× `Vec A n)

  open Defaults⟨first-part⟩ funU
  open CompositionNotations _∘_ public
  open DefaultAssoc′ _∘_ assoc swap first public

  infixr 3 _***_
  _***_ : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
  f *** g = < f × g >

  <id,tt> : ∀ {A} → A `→ A `× `⊤
  <id,tt> = <tt,id> ⁏ swap

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

  constVec⊤ : ∀ {n a} {A : ★_ a} {B} → (A → `⊤ `→ B) → Vec A n → `⊤ `→ `Vec B n
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

  rot-left : ∀ m {n A} → `Vec A (m + n) `→ `Vec A (n + m)
  rot-left m = splitAt m ⁏ swap ⁏ append

  rot-right : ∀ {m} n {A} → `Vec A (m + n) `→ `Vec A (n + m)
  rot-right {m} _ = rot-left m

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
  replicate⊤ _ = constVec⊤ (λ _ → id) (V.replicate {A = 𝟙} _)

  open Category cat public

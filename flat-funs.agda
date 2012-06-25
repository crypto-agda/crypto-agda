module flat-funs where

open import Data.Unit using (⊤)
open import Data.Nat.NP using (ℕ; zero; suc; _+_; _*_; 2^_; _⊔_)
open import Data.Fin using (Fin) renaming (_+_ to _+ᶠ_)
open import Data.Bool using (if_then_else_)
import Data.Vec.NP as V
import Level as L
import Function as F
import Data.Product as ×
open V using (Vec; []; _∷_; _++_)
open × using (_×_; _,_; proj₁; proj₂; uncurry)

open import Data.Bits using (Bits; _→ᵇ_)

open import universe

record FlatFuns {t} (T : Set t) : Set (L.suc t) where
  constructor mk
  field
    universe : Universe T
    El       : T → Set
    _`→_    : T → T → Set
  infix 0 _`→_
  open Universe universe public

record FlatFunsOps {t} {T : Set t} (♭Funs : FlatFuns T) : Set t where
  constructor mk
  open FlatFuns ♭Funs
  infixr 1 _>>>_
  infixr 3 _***_
  infixr 3 _&&&_
  field
    -- Functions
    id    : ∀ {A} → A `→ A
    _>>>_ : ∀ {A B C} → (A `→ B) → (B `→ C) → (A `→ C)
    const : ∀ {_A B} → El B → _A `→ B

    -- Bit (TODO check TODO use const to get 0 and 1: const 0b and const 1b)
    cond : ∀ {A} → `Bit `× A `× A `→ A

    -- Products
    <_,_> : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
    fst   : ∀ {A B} → A `× B `→ A
    snd   : ∀ {A B} → A `× B `→ B

    -- Unit
    tt : ∀ {_A} → _A `→ `⊤

    -- Vectors
    nil    : ∀ {_A B} → _A `→ `Vec B 0
    cons   : ∀ {n A} → (A `× `Vec A n) `→ `Vec A (1 + n)
    uncons : ∀ {n A} → `Vec A (1 + n) `→ (A `× `Vec A n)

  _∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C)
  f ∘ g = g >>> f

  _&&&_ : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  f &&& g = < f , g >

  <_×_> : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
  < f × g > = < fst >>> f , snd >>> g >

  _***_ : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
  f *** g = < f × g >

  swap : ∀ {A B} → (A `× B) `→ (B `× A)
  swap = < snd , fst >

  first : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B)
  first f = f *** id

  second : ∀ {A B C} → (B `→ C) → (A `× B) `→ (A `× C)
  second f = id *** f

  fork : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B
  fork f g = second < f , g > >>> cond

  -- In case you wonder... one can also derive cond with fork
  cond-on-top-of-fork : ∀ {A} → `Bit `× A `× A `→ A
  cond-on-top-of-fork = fork fst snd

  assoc : ∀ {A B C} → ((A `× B) `× C) `→ (A `× (B `× C))
  assoc = < fst >>> fst , first snd >

  assoc′ : ∀ {A B C} → (A `× (B `× C)) `→ ((A `× B) `× C)
  assoc′ = < second fst , snd >>> snd >

  <_`zip`_> : ∀ {A B C D E F} → ((A `× B) `→ C)
                           → ((D `× E) `→ F)
                           → ((A `× D) `× (B `× E)) `→ (C `× F)
  < f `zip` g > = < < fst × fst > >>> f ,
                    < snd × snd > >>> g >

  head : ∀ {n A} → `Vec A (1 + n) `→ A
  head = uncons >>> fst

  tail : ∀ {n A} → `Vec A (1 + n) `→ `Vec A n
  tail = uncons >>> snd

  <_∷_> : ∀ {m n A B} → (A `→ B) → (`Vec A m `→ `Vec B n)
                  → `Vec A (1 + m) `→ `Vec B (1 + n)
  < f ∷ g > = uncons >>> < f × g > >>> cons

  <_∷′_> : ∀ {n A B} → (A `→ B) → (A `→ `Vec B n)
                     → A `→ `Vec B (1 + n)
  < f ∷′ g > = < f , g > >>> cons

  foldl : ∀ {n A B} → (B `× A `→ B) → (B `× `Vec A n) `→ B
  foldl {zero}  f = fst
  foldl {suc n} f = second uncons
                >>> assoc′
                >>> first f
                >>> foldl f

  foldl₁ : ∀ {n A} → (A `× A `→ A) → `Vec A (1 + n) `→ A
  foldl₁ f = uncons >>> foldl f

  foldr : ∀ {n A B} → (A `× B `→ B) → (`Vec A n `× B) `→ B
  foldr {zero}  f = snd
  foldr {suc n} f = first uncons
                >>> assoc
                >>> second (foldr f)
                >>> f

  foldr₁ : ∀ {n A} → (A `× A `→ A) → `Vec A (1 + n) `→ A
  foldr₁ f = uncons >>> swap >>> foldr f

  map : ∀ {n A B} → (A `→ B) → (`Vec A n `→ `Vec B n)
  map {zero}  f = nil
  map {suc n} f = < f ∷ map f >

  zipWith : ∀ {n A B C} → ((A `× B) `→ C)
                        → (`Vec A n `× `Vec B n) `→ `Vec C n
  zipWith {zero}  f = nil
  zipWith {suc n} f = < uncons × uncons >
                  >>> < f `zip` (zipWith f) >
                  >>> cons

  zip : ∀ {n A B} → (`Vec A n `× `Vec B n) `→ `Vec (A `× B) n
  zip = zipWith id

  singleton : ∀ {A} → A `→ `Vec A 1
  singleton = < id , nil > >>> cons

  snoc : ∀ {n A} → (`Vec A n `× A) `→ `Vec A (1 + n)
  snoc {zero}  = snd >>> singleton
  snoc {suc n} = first uncons >>> assoc >>> second snoc >>> cons

  reverse : ∀ {n A} → `Vec A n `→ `Vec A n
  reverse {zero}  = nil
  reverse {suc n} = uncons >>> swap >>> first reverse >>> snoc

  append : ∀ {m n A} → (`Vec A m `× `Vec A n) `→ `Vec A (m + n)
  append {zero}  = snd
  append {suc m} = first uncons
               >>> assoc
               >>> second append
               >>> cons

  splitAt : ∀ m {n A} → `Vec A (m + n) `→ (`Vec A m `× `Vec A n)
  splitAt zero    = < nil , id >
  splitAt (suc m) = uncons
                >>> second (splitAt m)
                >>> assoc′
                >>> first cons

  take : ∀ m {n A} → `Vec A (m + n) `→ `Vec A m
  take zero    = nil
  take (suc m) = < id ∷ take m >

  drop : ∀ m {n A} → `Vec A (m + n) `→ `Vec A n
  drop zero    = id
  drop (suc m) = tail >>> drop m

  folda : ∀ n {A} → (A `× A `→ A) → `Vec A (2^ n) `→ A
  folda zero    f = head
  folda (suc n) f = splitAt (2^ n) >>> < folda n f × folda n f > >>> f

  init : ∀ {n A} → `Vec A (1 + n) `→ `Vec A n
  init {zero}  = nil
  init {suc n} = < id ∷ init >

  last : ∀ {n A} → `Vec A (1 + n) `→ A
  last {zero}  = head
  last {suc n} = tail >>> last

  concat : ∀ {m n A} → `Vec (`Vec A m) n `→ `Vec A (n * m)
  concat {n = zero}  = nil
  concat {n = suc n} = uncons >>> second concat >>> append

  group : ∀ {A} n k → `Vec A (n * k) `→ `Vec (`Vec A k) n
  group zero    k = nil
  group (suc n) k = splitAt k >>> second (group n k) >>> cons

  bind : ∀ {m n A B} → (A `→ `Vec B m) → `Vec A n `→ `Vec B (n * m)
  bind f = map f >>> concat

  ⊛ : ∀ {n A B} → Vec (A `→ B) n → `Vec A n `→ `Vec B n
  ⊛ []       = nil
  ⊛ (f ∷ fs) = uncons >>> < f × ⊛ fs > >>> cons

  replicate : ∀ {n A} → A `→ `Vec A n
  replicate {zero}  = nil
  replicate {suc n} = < id , replicate > >>> cons

  module WithFin
    (`Fin : ℕ → T)
    (fz : ∀ {n _A} → _A `→ `Fin (suc n))
    (fs : ∀ {n} → `Fin n `→ `Fin (suc n))
    (elim-Fin0 : ∀ {A} → `Fin 0 `→ A)
    (elim-Fin1+ : ∀ {n A B} → (A `→ B) → (`Fin n `× A `→ B) → `Fin (suc n) `× A `→ B) where

    tabulate : ∀ {n A _B} → (`Fin n `→ A) → _B `→ `Vec A n
    tabulate {zero}  f = nil
    tabulate {suc n} f = < fz >>> f , tabulate (fs >>> f) > >>> cons

    lookup : ∀ {n A} → `Fin n `× `Vec A n `→ A
    lookup {zero}  = fst >>> elim-Fin0
    lookup {suc n} = elim-Fin1+ head (second tail >>> lookup)

    allFin : ∀ {n _A} → _A `→ `Vec (`Fin n) n
    allFin = tabulate id

-→- : Set → Set → Set
-→- A B = A → B

_→ᶠ_ : ℕ → ℕ → Set
_→ᶠ_ i o = Fin i → Fin o

mapArr : ∀ {s t} {S : Set s} {T : Set t} (F G : T → S)
          → (S → S → Set) → (T → T → Set)
mapArr F G _`→_ A B = F A `→ G B

fun♭Funs : FlatFuns Set
fun♭Funs = mk Set-U F.id -→-

module FunTypes = FlatFuns fun♭Funs

bitsFun♭Funs : FlatFuns ℕ
bitsFun♭Funs = mk Bits-U Bits _→ᵇ_

module BitsFunTypes = FlatFuns bitsFun♭Funs

finFun♭Funs : FlatFuns ℕ
finFun♭Funs = mk Fin-U Fin _→ᶠ_

module FinFunTypes = FlatFuns finFun♭Funs

fun♭Ops : FlatFunsOps fun♭Funs
fun♭Ops = mk F.id (λ f g x → g (f x)) F.const
             (λ { (b , x , y) → if b then x else y })
             ×.<_,_> proj₁ proj₂
             _ (F.const []) (uncurry _∷_) V.uncons

module FunOps = FlatFunsOps fun♭Ops

bitsFun♭Ops : FlatFunsOps bitsFun♭Funs
bitsFun♭Ops = mk id _>>>_ const condᵇ <_,_>ᵇ (λ {A} → V.take A)
                    (λ {A} → V.drop A) (const []) (const []) id id
  where
  open BitsFunTypes
  open FunOps
  <_,_>ᵇ : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  < f , g >ᵇ x = f x ++ g x
  condᵇ : ∀ {A} → `Bit `× A `× A `→ A
  condᵇ {A} (b ∷ xs) = if b then take A xs else drop A xs

module BitsFunOps = FlatFunsOps bitsFun♭Ops

×-♭Funs : ∀ {s t} {S : Set s} {T : Set t} → FlatFuns S → FlatFuns T → FlatFuns (S × T)
×-♭Funs funs-S funs-T = mk (×-U S.universe T.universe)
                           (λ { (A₀ , A₁) → S.El A₀ × T.El A₁ })
                           (λ { (A₀ , A₁) (B₀ , B₁) → (A₀ S.`→ B₀) × (A₁ T.`→ B₁) })
  where module S = FlatFuns funs-S
        module T = FlatFuns funs-T

×⊤-♭Funs : ∀ {s} {S : Set s} → FlatFuns S → FlatFuns ⊤ → FlatFuns S
×⊤-♭Funs funs-S funs-T = mk S.universe (λ A → S.El A × T.El _)
                            (λ A B → (A S.`→ B) × (_ T.`→ _))
  where module S = FlatFuns funs-S
        module T = FlatFuns funs-T

×-♭Ops : ∀ {s t} {S : Set s} {T : Set t} {funs-S : FlatFuns S} {funs-T : FlatFuns T}
         → FlatFunsOps funs-S → FlatFunsOps funs-T
         → FlatFunsOps (×-♭Funs funs-S funs-T)
×-♭Ops ops-S ops-T
  = mk (S.id , T.id) (×.zip S._>>>_ T._>>>_) < S.const × T.const > (S.cond , T.cond)
       (×.zip S.<_,_> T.<_,_>) (S.fst , T.fst) (S.snd , T.snd)
       (S.tt , T.tt) (S.nil , T.nil) (S.cons , T.cons) (S.uncons , T.uncons)
  where module S = FlatFunsOps ops-S
        module T = FlatFunsOps ops-T
        open FunOps

×⊤-♭Ops : ∀ {s} {S : Set s} {funs-S : FlatFuns S} {funs-⊤ : FlatFuns ⊤}
         → FlatFunsOps funs-S → FlatFunsOps funs-⊤
         → FlatFunsOps (×⊤-♭Funs funs-S funs-⊤)
×⊤-♭Ops ops-S ops-⊤
  = mk (S.id , T.id) (×.zip S._>>>_ T._>>>_) < S.const × T.const > (S.cond , T.cond)
       (×.zip S.<_,_> T.<_,_>) (S.fst , T.fst) (S.snd , T.snd)
       (S.tt , T.tt) (S.nil , T.nil) (S.cons , T.id) (S.uncons , T.id)
  where module S = FlatFunsOps ops-S
        module T = FlatFunsOps ops-⊤
        open FunOps

constFuns : Set → FlatFuns ⊤
constFuns A = mk ⊤-U (λ _ → A) (λ _ _ → A)

module ConstFunTypes A = FlatFuns (constFuns A)

timeOps : FlatFunsOps (constFuns ℕ)
timeOps = mk 0 _+_ (F.const 0) 1 _⊔_ 0 0 0 0 0 0

module TimeOps = FlatFunsOps timeOps

spaceOps : FlatFunsOps (constFuns ℕ)
spaceOps = mk 0 _+_ const 1 _+_ 0 0 0 0 0 0
  where open ConstFunTypes ℕ
        const : ∀ {_A B} → El B → _A `→ B
        const {_} {_} x = x

module SpaceOps = FlatFunsOps spaceOps

time×spaceOps : FlatFunsOps (constFuns (ℕ × ℕ))
time×spaceOps = ×⊤-♭Ops timeOps spaceOps

module Time×SpaceOps = FlatFunsOps time×spaceOps

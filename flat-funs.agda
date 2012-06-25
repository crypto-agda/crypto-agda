module flat-funs where

open import Data.Unit using (⊤)
open import Data.Nat.NP using (ℕ; zero; suc; _+_; _*_; 2^_; _⊔_)
open import Data.Fin using (Fin) renaming (_+_ to _+ᶠ_)
open import Data.Bool using (if_then_else_)
import Data.Vec.NP as V
import Level as L
import Function as F
import Data.Product as ×
import Relation.Binary.PropositionalEquality as ≡
open F using (const)
open V using (Vec; []; _∷_; _++_; [_])
open × using (_×_; _,_; proj₁; proj₂; uncurry)
open ≡ using (_≡_)

open import Data.Bits using (Bit; Bits; _→ᵇ_; 0b; 1b)

open import universe

record FlatFuns {t} (T : Set t) : Set (L.suc t) where
  constructor mk
  field
    universe : Universe T
    _`→_    : T → T → Set
  infix 0 _`→_
  open Universe universe public

record FlatFunsOps {t} {T : Set t} (♭Funs : FlatFuns T) : Set t where
  constructor mk
  open FlatFuns ♭Funs
  infixr 1 _∘_
  infixr 1 _⁏_
  infixr 1 _>>>_
  infixr 3 _***_
  infixr 3 _&&&_
  field
    -- Functions
    id : ∀ {A} → A `→ A
    _∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C)

    -- Bit
    <0b> <1b> : ∀ {_A} → _A `→ `Bit
    cond      : ∀ {A} → `Bit `× A `× A `→ A

    -- Products
    dup   : ∀ {A} → A `→ A `× A
    fst   : ∀ {A B} → A `× B `→ A
    snd   : ∀ {A B} → A `× B `→ B
    <_×_> : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
    swap  : ∀ {A B} → (A `× B) `→ (B `× A)
    assoc : ∀ {A B C} → ((A `× B) `× C) `→ (A `× (B `× C))

    -- Unit
    tt : ∀ {_A} → _A `→ `⊤
    <tt,> : ∀ {A} → A `→ `⊤ `× A

    -- Vectors
    nil    : ∀ {_A B} → _A `→ `Vec B 0
    cons   : ∀ {n A} → (A `× `Vec A n) `→ `Vec A (1 + n)
    uncons : ∀ {n A} → `Vec A (1 + n) `→ (A `× `Vec A n)

  _⁏_ : ∀ {A B C} → (A `→ B) → (B `→ C) → (A `→ C)
  f ⁏ g = g ∘ f

  _>>>_ : ∀ {A B C} → (A `→ B) → (B `→ C) → (A `→ C)
  f >>> g = f ⁏ g

  <_,_> : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  < f , g > = dup ⁏ < f × g >

  _&&&_ : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  f &&& g = < f , g >

  <_×_>-on-top-of-<,> : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
  < f × g >-on-top-of-<,> = < fst ⁏ f , snd ⁏ g >

  _***_ : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
  f *** g = < f × g >

  swap-on-top-<,> : ∀ {A B} → (A `× B) `→ (B `× A)
  swap-on-top-<,> = < snd , fst >

  first : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B)
  first f = < f × id >

  second : ∀ {A B C} → (B `→ C) → (A `× B) `→ (A `× C)
  second f = < id × f >

  fork : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B
  fork f g = second < f , g > ⁏ cond

  -- In case you wonder... one can also derive cond with fork
  cond-on-top-of-fork : ∀ {A} → `Bit `× A `× A `→ A
  cond-on-top-of-fork = fork fst snd

  constBit : ∀ {_A} → Bit → _A `→ `Bit
  constBit b = if b then <1b> else <0b>

  <,tt> : ∀ {A} → A `→ A `× `⊤
  <,tt> = <tt,> ⁏ swap

  assoc-default : ∀ {A B C} → ((A `× B) `× C) `→ (A `× (B `× C))
  assoc-default = < fst ⁏ fst , first snd >

  assoc′ : ∀ {A B C} → (A `× (B `× C)) `→ ((A `× B) `× C)
  assoc′ = < second fst , snd ⁏ snd >

  <_`zip`_> : ∀ {A B C D E F} → ((A `× B) `→ C)
                           → ((D `× E) `→ F)
                           → ((A `× D) `× (B `× E)) `→ (C `× F)
  < f `zip` g > = < < fst × fst > ⁏ f ,
                    < snd × snd > ⁏ g >

  head : ∀ {n A} → `Vec A (1 + n) `→ A
  head = uncons ⁏ fst

  tail : ∀ {n A} → `Vec A (1 + n) `→ `Vec A n
  tail = uncons ⁏ snd

  <_∷_> : ∀ {m n A B} → (A `→ B) → (`Vec A m `→ `Vec B n)
                  → `Vec A (1 + m) `→ `Vec B (1 + n)
  < f ∷ g > = uncons ⁏ < f × g > ⁏ cons

  <_∷′_> : ∀ {n A B} → (A `→ B) → (A `→ `Vec B n)
                     → A `→ `Vec B (1 + n)
  < f ∷′ g > = < f , g > ⁏ cons

  ⊛ : ∀ {n A B} → Vec (A `→ B) n → `Vec A n `→ `Vec B n
  ⊛ []       = nil
  ⊛ (f ∷ fs) = < f ∷ ⊛ fs >

  ⊛′ : ∀ {n A B} → Vec (A `→ B) n → A `→ `Vec B n
  ⊛′ []       = nil
  ⊛′ (f ∷ fs) = < f ∷′ ⊛′ fs >

  constVec : ∀ {n b _A} {B : Set b} {C} → (B → _A `→ C) → Vec B n → _A `→ `Vec C n
  constVec f xs = ⊛′ (V.map f xs)

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

  map : ∀ {n A B} → (A `→ B) → (`Vec A n `→ `Vec B n)
  map f = ⊛ (V.replicate f)

  zipWith : ∀ {n A B C} → ((A `× B) `→ C)
                        → (`Vec A n `× `Vec B n) `→ `Vec C n
  zipWith {zero}  f = nil
  zipWith {suc n} f = < uncons × uncons >
                    ⁏ < f `zip` (zipWith f) >
                    ⁏ cons

  zip : ∀ {n A B} → (`Vec A n `× `Vec B n) `→ `Vec (A `× B) n
  zip = zipWith id

  <,nil> : ∀ {A B} → A `→ A `× `Vec B 0
  <,nil> = <,tt> ⁏ second nil

  singleton : ∀ {A} → A `→ `Vec A 1
  singleton = <,nil> ⁏ cons

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
  splitAt zero    = < nil , id >
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

  module WithFin
    (`Fin : ℕ → T)
    (fz : ∀ {n _A} → _A `→ `Fin (suc n))
    (fs : ∀ {n} → `Fin n `→ `Fin (suc n))
    (elim-Fin0 : ∀ {A} → `Fin 0 `→ A)
    (elim-Fin1+ : ∀ {n A B} → (A `→ B) → (`Fin n `× A `→ B) → `Fin (suc n) `× A `→ B) where

    tabulate : ∀ {n A _B} → (`Fin n `→ A) → _B `→ `Vec A n
    tabulate {zero}  f = nil
    tabulate {suc n} f = < fz ⁏ f , tabulate (fs ⁏ f) > ⁏ cons

    lookup : ∀ {n A} → `Fin n `× `Vec A n `→ A
    lookup {zero}  = fst ⁏ elim-Fin0
    lookup {suc n} = elim-Fin1+ head (second tail ⁏ lookup)

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
fun♭Funs = mk Set-U -→-

module FunTypes = FlatFuns fun♭Funs

bitsFun♭Funs : FlatFuns ℕ
bitsFun♭Funs = mk Bits-U _→ᵇ_

module BitsFunTypes = FlatFuns bitsFun♭Funs

finFun♭Funs : FlatFuns ℕ
finFun♭Funs = mk Fin-U _→ᶠ_

module FinFunTypes = FlatFuns finFun♭Funs

fun♭Ops : FlatFunsOps fun♭Funs
fun♭Ops = mk F.id F._∘′_
             (F.const 0b) (F.const 1b) (λ { (b , x , y) → if b then x else y })
             (λ x → x , x) proj₁ proj₂ (λ f g → ×.map f g)
             ×.swap (λ {((x , y) , z) → x , (y , z) }) _ (λ x → _ , x) (F.const []) (uncurry _∷_) V.uncons

module FunOps = FlatFunsOps fun♭Ops

bitsFun♭Ops : FlatFunsOps bitsFun♭Funs
bitsFun♭Ops = mk id _∘_
                 (const [ 0b ]) (const [ 1b ]) condᵇ
                 dupᵇ fstᵇ (λ {x} → sndᵇ {x}) <_×_>ᵇ
                 (λ {x} → swapᵇ {x}) (λ {x} → assocᵇ {x}) (const []) id (const []) id id
  where
  open BitsFunTypes
  open FunOps
  fstᵇ : ∀ {A B} → A `× B `→ A
  fstᵇ {A} = V.take A
  sndᵇ : ∀ {A B} → A `× B `→ B
  sndᵇ {A} = V.drop A
  dupᵇ : ∀ {A} → A `→ A `× A
  dupᵇ xs = xs ++ xs
  <_×_>ᵇ : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
  <_×_>ᵇ {A} f g x = f (take A x) ++ g (drop A x)
  condᵇ : ∀ {A} → `Bit `× A `× A `→ A
  condᵇ {A} (b ∷ xs) = if b then take A xs else drop A xs
  swapᵇ : ∀ {A B} → (A `× B) `→ (B `× A)
  swapᵇ {A} xs = drop A xs ++ take A xs
  assocᵇ : ∀ {A B C} → ((A `× B) `× C) `→ (A `× (B `× C))
  assocᵇ {A} {B} xs = take A (take (A + B) xs) ++ (drop A (take (A + B) xs) ++ drop (A + B) xs) -- < fstᵇ ⁏ fstᵇ , first sndᵇ >

module BitsFunOps = FlatFunsOps bitsFun♭Ops

×-♭Funs : ∀ {s t} {S : Set s} {T : Set t} → FlatFuns S → FlatFuns T → FlatFuns (S × T)
×-♭Funs funs-S funs-T = mk (×-U S.universe T.universe)
                           (λ { (A₀ , A₁) (B₀ , B₁) → (A₀ S.`→ B₀) × (A₁ T.`→ B₁) })
  where module S = FlatFuns funs-S
        module T = FlatFuns funs-T

×⊤-♭Funs : ∀ {s} {S : Set s} → FlatFuns S → FlatFuns ⊤ → FlatFuns S
×⊤-♭Funs funs-S funs-T = mk S.universe (λ A B → (A S.`→ B) × (_ T.`→ _))
  where module S = FlatFuns funs-S
        module T = FlatFuns funs-T

×-♭Ops : ∀ {s t} {S : Set s} {T : Set t} {funs-S : FlatFuns S} {funs-T : FlatFuns T}
         → FlatFunsOps funs-S → FlatFunsOps funs-T
         → FlatFunsOps (×-♭Funs funs-S funs-T)
×-♭Ops ops-S ops-T
  = mk (S.id , T.id) (×.zip S._∘_ T._∘_)
       (S.<0b> , T.<0b>) (S.<1b> , T.<1b>) (S.cond , T.cond)
       (S.dup , T.dup) (S.fst , T.fst) (S.snd , T.snd) (×.zip S.<_×_> T.<_×_>)
       (S.swap , T.swap) (S.assoc , T.assoc)
       (S.tt , T.tt) (S.<tt,> , T.<tt,>)
       (S.nil , T.nil) (S.cons , T.cons) (S.uncons , T.uncons)
  where module S = FlatFunsOps ops-S
        module T = FlatFunsOps ops-T
        open FunOps

×⊤-♭Ops : ∀ {s} {S : Set s} {funs-S : FlatFuns S} {funs-⊤ : FlatFuns ⊤}
         → FlatFunsOps funs-S → FlatFunsOps funs-⊤
         → FlatFunsOps (×⊤-♭Funs funs-S funs-⊤)
×⊤-♭Ops ops-S ops-⊤
  = mk (S.id , T.id) (×.zip S._∘_ T._∘_)
       (S.<0b> , T.<0b>) (S.<1b> , T.<1b>) (S.cond , T.cond)
       (S.dup , T.dup) (S.fst , T.fst) (S.snd , T.snd) (×.zip S.<_×_> T.<_×_>)
       (S.swap , T.swap) (S.assoc , T.assoc)
       (S.tt , T.tt) (S.<tt,> , T.<tt,>)
       (S.nil , T.nil) (S.cons , T.id) (S.uncons , T.id)
  where module S = FlatFunsOps ops-S
        module T = FlatFunsOps ops-⊤
        open FunOps

constFuns : Set → FlatFuns ⊤
constFuns A = mk ⊤-U (λ _ _ → A)

module ConstFunTypes A = FlatFuns (constFuns A)

timeOps : FlatFunsOps (constFuns ℕ)
timeOps = record {
            id = 0; _∘_ = _+_;
            <0b> = 0; <1b> = 0; cond = 1;
            dup = 0; fst = 0; snd = 0; <_×_> = _⊔_; swap = 0; assoc = 0;
            tt = 0; <tt,> = 0;
            nil = 0; cons = 0; uncons = 0 }

module TimeOps = FlatFunsOps timeOps

spaceOps : FlatFunsOps (constFuns ℕ)
spaceOps = record {
             id = 0; _∘_ = _+_;
             <0b> = 0; <1b> = 0; cond = 1;
             dup = 1; fst = 0; snd = 0; <_×_> = _+_; swap = 0; assoc = 0;
             tt = 0; <tt,> = 0;
             nil = 0; cons = 0; uncons = 0 }

module SpaceOps where
  Space = ℕ
  open FlatFunsOps spaceOps public

  singleton≡0 : singleton ≡ 0
  singleton≡0 = ≡.refl

  snoc≡0 : ∀ n → snoc {n} ≡ 0
  snoc≡0 zero = ≡.refl
  snoc≡0 (suc n) rewrite snoc≡0 n = ≡.refl

  reverse≡0 : ∀ n → reverse {n} ≡ 0
  reverse≡0 zero = ≡.refl
  reverse≡0 (suc n) rewrite snoc≡0 n | reverse≡0 n = ≡.refl

time×spaceOps : FlatFunsOps (constFuns (ℕ × ℕ))
time×spaceOps = ×⊤-♭Ops timeOps spaceOps

module Time×SpaceOps = FlatFunsOps time×spaceOps

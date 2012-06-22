module flat-funs where

open import Data.Nat.NP
import Data.Vec as V
open V using (Vec; []; _∷_)
open import Data.Bits using (Bits)
import Level as L
import Function as F
open import composable
open import vcomp
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
  infixr 1 _>>>_
  infixr 3 _***_
  infixr 3 _&&&_
  field
    idO : ∀ {A} → A `→ A

    _>>>_ : ∀ {A B C} → (A `→ B) → (B `→ C) → (A `→ C)

    _***_ : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)

    _&&&_ : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C

    fst : ∀ {A B} → A `× B `→ A
    snd : ∀ {A B} → A `× B `→ B

    tt : ∀ {_A} → _A `→ `⊤

    nil : ∀ {_A B} → _A `→ `Vec B 0
    cons : ∀ {n A} → (A `× `Vec A n) `→ `Vec A (1 + n)

    uncons : ∀ {n A} → `Vec A (1 + n) `→ (A `× `Vec A n)

    constBits : ∀ {n _A} → Bits n → _A `→ `Bits n

  <_,_> : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  < f , g > = f &&& g

  <_×_> : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
  < f × g > = f *** g

  swap : ∀ {A B} → (A `× B) `→ (B `× A)
  swap = < snd , fst >

  first : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B)
  first f = f *** idO

  second : ∀ {A B C} → (B `→ C) → (A `× B) `→ (A `× C)
  second f = idO *** f

  assoc : ∀ {A B C} → ((A `× B) `× C) `→ (A `× (B `× C))
  assoc = < fst >>> fst , first snd >

  assoc′ : ∀ {A B C} → (A `× (B `× C)) `→ ((A `× B) `× C)
  assoc′ = < second fst , snd >>> snd >

  `×-zip : ∀ {A B C D E F} → ((A `× B) `→ C)
                           → ((D `× E) `→ F)
                           → ((A `× D) `× (B `× E)) `→ (C `× F)
  `×-zip f g = < < fst >>> fst , snd >>> fst > >>> f ,
                 < fst >>> snd , snd >>> snd > >>> g >

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
                  >>> `×-zip f (zipWith f)
                  >>> cons

  zip : ∀ {n A B} → (`Vec A n `× `Vec B n) `→ `Vec (A `× B) n
  zip = zipWith idO

  singleton : ∀ {A} → A `→ `Vec A 1
  singleton = < idO , nil > >>> cons

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
  splitAt zero    = < nil , idO >
  splitAt (suc m) = uncons
                >>> second (splitAt m)
                >>> assoc′
                >>> first cons

  take : ∀ m {n A} → `Vec A (m + n) `→ `Vec A m
  take zero    = nil
  take (suc m) = < idO ∷ take m >

  drop : ∀ m {n A} → `Vec A (m + n) `→ `Vec A n
  drop zero    = idO
  drop (suc m) = tail >>> drop m

  folda : ∀ n {A} → (A `× A `→ A) → `Vec A (2^ n) `→ A
  folda zero    f = head
  folda (suc n) f = splitAt (2^ n) >>> < folda n f × folda n f > >>> f

  init : ∀ {n A} → `Vec A (1 + n) `→ `Vec A n
  init {zero}  = nil
  init {suc n} = < idO ∷ init >

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
  replicate {suc n} = < idO , replicate > >>> cons

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
    allFin = tabulate idO

open import Data.Unit using (⊤)
open import Data.Vec
open import Data.Bits
open import Data.Fin using (Fin) renaming (_+_ to _+ᶠ_)
open import Data.Product renaming (zip to ×-zip; map to ×-map)
open import Function

-→- : Set → Set → Set
-→- A B = A → B

_→ᶠ_ : ℕ → ℕ → Set
_→ᶠ_ i o = Fin i → Fin o

mapArr : ∀ {s t} {S : Set s} {T : Set t} (F G : T → S)
          → (S → S → Set) → (T → T → Set)
mapArr F G _`→_ A B = F A `→ G B

fun♭Funs : FlatFuns Set
fun♭Funs = mk Set-U -→-

bitsFun♭Funs : FlatFuns ℕ
bitsFun♭Funs = mk Bits-U _→ᵇ_

finFun♭Funs : FlatFuns ℕ
finFun♭Funs = mk Fin-U _→ᶠ_

fun♭Ops : FlatFunsOps fun♭Funs
fun♭Ops = mk id (λ f g x → g (f x)) (λ f g → ×-map f g) _&&&_ proj₁ proj₂ _ (const []) (uncurry _∷_) uncons const
  where
  _&&&_ : ∀ {A B C : Set} → (A → B) → (A → C) → A → B × C
  (f &&& g) x = (f x , g x)
  uncons : ∀ {n A} → Vec A (1 + n) → (A × Vec A n)
  uncons (x ∷ xs) = x , xs

bitsFun♭Ops : FlatFunsOps bitsFun♭Funs
bitsFun♭Ops = mk id (λ f g → g ∘ f) (VComposable._***_ bitsFunVComp) _&&&_ (λ {A} → take A)
                    (λ {A} → drop A) (const []) (const []) id id (λ xs _ → concat (map [_] xs) {- ugly? -})
  where
  open FlatFuns bitsFun♭Funs
  _&&&_ : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  (f &&& g) x = (f x ++ g x)

×-♭Funs : ∀ {s t} {S : Set s} {T : Set t} → FlatFuns S → FlatFuns T → FlatFuns (S × T)
×-♭Funs funs-S funs-T = mk (×-U S.universe T.universe)
                           (λ { (A₀ , A₁) (B₀ , B₁) → (A₀ S.`→ B₀) × (A₁ T.`→ B₁) })
  where module S = FlatFuns funs-S
        module T = FlatFuns funs-T

×⊤-♭Funs : ∀ {s} {S : Set s} → FlatFuns S → FlatFuns ⊤ → FlatFuns S
×⊤-♭Funs funs-S funs-T = mk S.universe
                           (λ A B → (A S.`→ B) × (_ T.`→ _))
  where module S = FlatFuns funs-S
        module T = FlatFuns funs-T

×-♭Ops : ∀ {s t} {S : Set s} {T : Set t} {funs-S : FlatFuns S} {funs-T : FlatFuns T}
         → FlatFunsOps funs-S → FlatFunsOps funs-T
         → FlatFunsOps (×-♭Funs funs-S funs-T)
×-♭Ops ops-S ops-T = mk (S.idO , T.idO) (×-zip S._>>>_ T._>>>_) (×-zip S._***_ T._***_)
                        (×-zip S._&&&_ T._&&&_) (S.fst , T.fst) (S.snd , T.snd)
                        (S.tt , T.tt) (S.nil , T.nil) (S.cons , T.cons)
                        (S.uncons , T.uncons) (S.constBits &&& T.constBits)
  where module S = FlatFunsOps ops-S
        module T = FlatFunsOps ops-T
        open FlatFunsOps fun♭Ops

×⊤-♭Ops : ∀ {s} {S : Set s} {funs-S : FlatFuns S} {funs-⊤ : FlatFuns ⊤}
         → FlatFunsOps funs-S → FlatFunsOps funs-⊤
         → FlatFunsOps (×⊤-♭Funs funs-S funs-⊤)
×⊤-♭Ops ops-S ops-⊤ = mk (S.idO , T.idO) (×-zip S._>>>_ T._>>>_) (×-zip S._***_ T._***_)
                         (×-zip S._&&&_ T._&&&_) (S.fst , T.fst) (S.snd , T.snd)
                         (S.tt , T.tt) (S.nil , T.nil) (S.cons , T.idO)
                         (S.uncons , T.idO) (S.constBits &&& T.constBits)
  where module S = FlatFunsOps ops-S
        module T = FlatFunsOps ops-⊤
        open FlatFunsOps fun♭Ops

constFuns : Set → FlatFuns ⊤
constFuns A = mk ⊤-U (λ _ _ → A)

timeOps : FlatFunsOps (constFuns ℕ)
timeOps = mk 0 _+_ _⊔_ _⊔_ 0 0 0 0 0 0 (const 0)

spaceOps : FlatFunsOps (constFuns ℕ)
spaceOps = mk 0 _+_ _+_ _+_ 0 0 0 0 0 0 (λ {n} _ → n)

time×spaceOps : FlatFunsOps (constFuns (ℕ × ℕ))
time×spaceOps = ×⊤-♭Ops timeOps spaceOps

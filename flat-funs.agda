module flat-funs where

open import Data.Nat
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
  field
    idO : ∀ {A} → A `→ A

    _>>>_ : ∀ {A B C} → (A `→ B) → (B `→ C) → (A `→ C)

    _***_ : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)

    -- Fanout
    _&&&_ : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C

    fst : ∀ {A B} → A `× B `→ A
    snd : ∀ {A B} → A `× B `→ B

    constBits : ∀ {n} → Bits n → `⊤ `→ `Bits n

  <_,_> : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  < f , g > = f &&& g

  <_×_> : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
  < f × g > = f *** g

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
fun♭Ops = mk id (λ f g x → g (f x)) (λ f g → ×-map f g) _&&&_ proj₁ proj₂ const
  where
  _&&&_ : ∀ {A B C : Set} → (A → B) → (A → C) → A → B × C
  (f &&& g) x = (f x , g x)

bitsFun♭Ops : FlatFunsOps bitsFun♭Funs
bitsFun♭Ops = mk id (λ f g → g ∘ f) (VComposable._***_ bitsFunVComp) _&&&_ (λ {A} → take A)
                    (λ {A} → drop A) (λ xs _ → xs ++ [] {- ugly? -})
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
                        (S.constBits &&& T.constBits)
  where module S = FlatFunsOps ops-S
        module T = FlatFunsOps ops-T
        open FlatFunsOps fun♭Ops

×⊤-♭Ops : ∀ {s} {S : Set s} {funs-S : FlatFuns S} {funs-⊤ : FlatFuns ⊤}
         → FlatFunsOps funs-S → FlatFunsOps funs-⊤
         → FlatFunsOps (×⊤-♭Funs funs-S funs-⊤)
×⊤-♭Ops ops-S ops-⊤ = mk (S.idO , T.idO) (×-zip S._>>>_ T._>>>_) (×-zip S._***_ T._***_)
                         (×-zip S._&&&_ T._&&&_) (S.fst , T.fst) (S.snd , T.snd)
                         (S.constBits &&& T.constBits)
  where module S = FlatFunsOps ops-S
        module T = FlatFunsOps ops-⊤
        open FlatFunsOps fun♭Ops


constFuns : Set → FlatFuns ⊤
constFuns A = mk ⊤-U (λ _ _ → A)

timeOps : FlatFunsOps (constFuns ℕ)
timeOps = mk 0 _+_ _⊔_ _⊔_ 0 0 (const 0)

spaceOps : FlatFunsOps (constFuns ℕ)
spaceOps = mk 0 _+_ _+_ _+_ 0 0 (λ {n} _ → n)

time×spaceOps : FlatFunsOps (constFuns (ℕ × ℕ))
time×spaceOps = ×⊤-♭Ops timeOps spaceOps

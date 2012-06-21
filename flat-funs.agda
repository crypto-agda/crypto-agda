module flat-funs where

open import Data.Nat
import Level as L
open import composable
open import vcomp

record FlatFuns {t} (T : Set t) : Set (L.suc t) where
  constructor mk
  field
    `⊤    : T
    `Bit  : T
    _`×_  : T → T → T
    _`^_  : T → ℕ → T
    _`→_  : T → T → Set

  `Vec : T → ℕ → T
  `Vec A n = A `^ n

  `Bits : ℕ → T
  `Bits n = `Bit `^ n

  infixr 2 _`×_
  infixl 2 _`^_
  infix 0 _`→_

record FlatFunsOps {t} {T : Set t} (♭Funs : FlatFuns T) : Set t where
  constructor mk
  open FlatFuns ♭Funs
  field
    idO : ∀ {A} → A `→ A
    isComposable  : Composable  _`→_
    isVComposable : VComposable _`×_ _`→_

    -- Fanout
    _&&&_ : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C

    fst : ∀ {A B} → A `× B `→ A
    snd : ∀ {A B} → A `× B `→ B

  open Composable isComposable
  open VComposable isVComposable

  <_,_> : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  < f , g > = f &&& g

  <_×_> : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
  < f × g > = f *** g

  open Composable isComposable public
  open VComposable isVComposable public

open import Data.Unit using (⊤)
open import Data.Vec
open import Data.Bits
open import Data.Product
open import Function

fun♭Funs : FlatFuns Set
fun♭Funs = mk ⊤ Bit _×_ Vec (λ A B → A → B)

bitsFun♭Funs : FlatFuns ℕ
bitsFun♭Funs = mk 0 1 _+_ _*_ (λ i o → Bits i → Bits o)

fun♭Ops : FlatFunsOps fun♭Funs
fun♭Ops = mk id funComp funVComp _&&&_ proj₁ proj₂
  where
  _&&&_ : ∀ {A B C : Set} → (A → B) → (A → C) → A → B × C
  (f &&& g) x = (f x , g x)

bitsFun♭Ops : FlatFunsOps bitsFun♭Funs
bitsFun♭Ops = mk id bitsFunComp bitsFunVComp _&&&_ (λ {A} → take A) (λ {A} → drop A)
  where
  open FlatFuns bitsFun♭Funs
  _&&&_ : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  (f &&& g) x = (f x ++ g x)

×-♭Funs : ∀ {s t} {S : Set s} {T : Set t} → FlatFuns S → FlatFuns T → FlatFuns (S × T)
×-♭Funs funs-S funs-T = ?
  where module S = FlatFuns funs-S
        module T = FlatFuns funs-T

×-♭Ops : ∀ {s t} {S : Set s} {T : Set t} {funs-S : FlatFuns S} {funs-T : FlatFuns T}
         → FlatFunsOps funs-S → FlatFunsOps funs-T
         → FlatFunsOps (×-♭Funs funs-S funs-T)
×-♭Ops ops-S ops-T = ?
  where module S = FlatFunsOps ops-S
        module T = FlatFunsOps ops-T

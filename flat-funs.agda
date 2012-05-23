module flat-funs where

open import Data.Nat
import Level as L
open import composable
open import vcomp

record FlatFuns {t} (T : Set t) : Set (L.suc t) where
  constructor mk
  field
    `Bits : ℕ → T
    `Bit  : T
    _`×_  : T → T → T
    _`→_  : T → T → Set
  infixr 2 _`×_
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

  open FlatFuns ♭Funs public
  open Composable isComposable public
  open VComposable isVComposable public

open import Data.Bits
open import Data.Product
open import Function

fun♭Funs : FlatFuns Set
fun♭Funs = mk Bits Bit _×_ (λ A B → A → B)

fun♭Ops : FlatFunsOps fun♭Funs
fun♭Ops = mk id funComp funVComp _&&&_
  where
  _&&&_ : ∀ {A B C : Set} → (A → B) → (A → C) → A → B × C
  (f &&& g) x = (f x , g x)

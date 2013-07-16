open import Type
open import Function
open import Data.Nat.NP using (ℕ; module ℕ°)
open import Data.Fin.NP as Fin using (Fin; inject+; raise; bound; free)
open import Data.Vec.NP using (lookup)
open import FunUniverse.Data
open import FunUniverse.Core
open import FunUniverse.Rewiring.Linear
open import FunUniverse.Category
open import FunUniverse.Category.Op
open import FunUniverse.Fin

module FunUniverse.Fin.Op where

_ᶠ→_ : (i o : ℕ) → ★
i ᶠ→ o = Fin o → Fin i

finOpFunU : FunUniverse ℕ
finOpFunU = Bits-U , _ᶠ→_

finOpCat : Category _ᶠ→_
finOpCat = op finCat

open FunUniverse finOpFunU
open Cong-*1 _`→_

finOpLinRewiring : LinRewiring finOpFunU
finOpLinRewiring = mk finOpCat first (λ {x} → swap {x}) (λ {x} → assoc {x}) id id <_×_> (λ {x} → second {x}) id id id id
  where
    -- NOTE that doing:
    --   swap {A} {B} rewrite ℕ°.+-comm A B = id
    -- would be totally wrong.
    swap : ∀ {A B} → (A `× B) `→ (B `× A)
    swap {A} {B} x with Fin.cmp B A x
    swap {A} {B} ._ | Fin.bound y = raise A y
    swap {A} {B} ._ | Fin.free  y = inject+ B y

    -- Since the order of elements is preserved this is OK to rewrite
    assoc : ∀ {A B C} → ((A `× B) `× C) `→ (A `× (B `× C))
    assoc {A} {B} {C} rewrite ℕ°.+-assoc A B C = id

    <_×_>  : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
    <_×_> {A} {B} {C} {D} f g x with Fin.cmp C D x
    <_×_> {A} {B} {C} {D} f g ._ | Fin.bound y = inject+ B (f y)
    <_×_> {A} {B} {C} {D} f g ._ | Fin.free  y = raise A   (g y)

    idᶠ : ∀ {A} → A `→ A
    idᶠ = id

    first : ∀ {A B C} → (A `→ B) → (A `× C) `→ (B `× C)
    first f = < f × id >

    second : ∀ {A B C} → (B `→ C) → (A `× B) `→ (A `× C)
    second {A} f = < idᶠ {A} × f >

finOpRewiring : Rewiring finOpFunU
finOpRewiring = mk finOpLinRewiring (λ ()) dup (λ()) (λ f g → dup ⁏ < f × g >) (inject+ _) (λ {x} → raise x) cong-*1 (cong-*1 ∘ flip lookup)
  where
    open LinRewiring finOpLinRewiring using (<_×_>; _⁏_)
    dup : ∀ {A} → A `→ (A `× A)
    dup {A} x with Fin.cmp A A x
    dup    ._ | Fin.bound y = y
    dup    ._ | Fin.free  y = y

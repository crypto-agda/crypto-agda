{-# OPTIONS --without-K #-}
open import FunUniverse.Core
import      FunUniverse.Category.Op as CatOp
open import FunUniverse.Rewiring.Linear

open import Data.Nat

module FunUniverse.Inverse {t} {T : Set t}
                           (funU : FunUniverse T)
                           (bijU : Bijective funU) where

opU : FunUniverse T
opU = OpFunU.opFunU funU

open FunUniverse opU

invLinRewiring : LinRewiring funU → LinRewiring opU
invLinRewiring linRewiring = mk (CatOp.op L.cat)
                                first swap assoc <tt,id> snd<tt,>
                                <_×_> second tt→[] []→tt <∷> uncons
  where
    module L = LinRewiring linRewiring
    -- Functions
    id : ∀ {A} → A `→ A
    id = L.id

    _∘_   : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C)
    f ∘ g = g L.∘ f

    -- Products (group 2 primitive functions or derived from group 1)
    first   : ∀ {A B C} → (A `→ C) → (A `× B) `→ (C `× B)
    first f = L.first f

    swap : ∀ {A B} → (A `× B) `→ (B `× A)
    swap = L.swap

    assoc : ∀ {A B C} → ((A `× B) `× C) `→ (A `× (B `× C))
    assoc = L.assoc′

    <tt,id> : ∀ {A} → A `→ `𝟙 `× A
    <tt,id> = L.snd<tt,>

    snd<tt,> : ∀ {A} → `𝟙 `× A `→ A
    snd<tt,> = L.<tt,id>

    -- Products (derived from group 1 or 2)
    <_×_>     : ∀ {A B C D} → (A `→ C) → (B `→ D) → (A `× B) `→ (C `× D)
    < f × g > = L.< f × g >

    second   : ∀ {A B C} → (B `→ C) → (A `× B) `→ (A `× C)
    second f = L.second f

    -- Vectors
    tt→[] : ∀ {A} → `𝟙 `→ `Vec A 0
    tt→[] = L.[]→tt

    []→tt : ∀ {A} → `Vec A 0 `→ `𝟙
    []→tt = L.tt→[]

    <∷> : ∀ {n A} → (A `× `Vec A n) `→ `Vec A (1 + n)
    <∷> = L.uncons

    uncons : ∀ {n A} → `Vec A (1 + n) `→ (A `× `Vec A n)
    uncons = L.<∷>

invHasBijFork : HasBijFork funU → HasBijFork opU
invHasBijFork hasBijFork = mk F.bijFork
  where module F = HasBijFork hasBijFork

invHasXor : HasXor funU → HasXor opU
invHasXor hasXor = mk H.⟨⊕_⟩
  where module H = HasXor hasXor

invU : Bijective funU → Bijective opU
invU bijective = mk (invLinRewiring linRewiring)
                    (invHasBijFork hasBijFork)
                    (invHasXor hasXor)
  where open Bijective bijective

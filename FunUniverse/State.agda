{-# OPTIONS --without-K #-}
open import Type
open import Data.Nat.NP
open import Data.Bits hiding (rewire; rewireTbl)
open import Data.Fin using (Fin)
open import FunUniverse.Data
open import FunUniverse.Core

module FunUniverse.State {t} {T : Set t} (S : T) (funU : FunUniverse T) where

open FunUniverse funU

infixr 0 _→ˢ_
_→ˢ_ : T → T → ★
A →ˢ B = A `× S `→ B `× S

_→ˢᵇ_ : ℕ → ℕ → ★
i →ˢᵇ o = `Bits i →ˢ `Bits o

Endoˢ : T → ★
Endoˢ A = A →ˢ A

funUˢ : FunUniverse T
funUˢ = universe , _→ˢ_

module LinRewiringˢ (linRewiring : LinRewiring funU) where

  open LinRewiring linRewiring

  idˢ : ∀ {A} → A →ˢ A
  idˢ = id

  _∘ˢ_ : ∀ {A B C} → (B →ˢ C) → (A →ˢ B) → (A →ˢ C)
  _∘ˢ_ = _∘_

  firstˢ : ∀ {A B C} → (A →ˢ C) → (A `× B) →ˢ (C `× B)
  firstˢ f = {!assoc ⁏ second swap ⁏ first f ⁏ second swap ⁏ assoc′!}

  secondˢ : ∀ {A B C} → (B →ˢ C) → (A `× B) →ˢ (A `× C)
  secondˢ f = assoc ⁏ second f ⁏ assoc′

  <_×_>ˢ  : ∀ {A B C D} → (A →ˢ C) → (B →ˢ D) → (A `× B) →ˢ (C `× D)
  < f × g >ˢ = {!assoc ⁏ second swap ⁏ first f ⁏ second swap ⁏ second g ⁏ assoc′!}

  swapˢ : ∀ {A B} → (A `× B) →ˢ (B `× A)
  swapˢ = first swap

  assocˢ : ∀ {A B C} → ((A `× B) `× C) →ˢ (A `× (B `× C))
  assocˢ = first assoc

  <tt,id>ˢ : ∀ {A} → A →ˢ (`⊤ `× A)
  <tt,id>ˢ = first <tt,id>

  snd<tt,>ˢ : ∀ {A} → (`⊤ `× A) →ˢ A
  snd<tt,>ˢ = {!first snd<tt,>ˢ!}

  tt→[]ˢ : ∀ {A} → `⊤ →ˢ `Vec A 0
  tt→[]ˢ = first tt→[]

  []→ttˢ : ∀ {A} → `Vec A 0 →ˢ `⊤
  []→ttˢ = first []→tt

  <∷>ˢ : ∀ {n A} → (A `× `Vec A n) →ˢ `Vec A (1 + n)
  <∷>ˢ = first <∷>

  unconsˢ : ∀ {n A} → `Vec A (1 + n) →ˢ (A `× `Vec A n)
  unconsˢ = first uncons

  linRewiringˢ : LinRewiring funUˢ
  linRewiringˢ = {!!}

module Rewiringˢ (rewiring : Rewiring funU) where
  open Rewiring rewiring
  open LinRewiringˢ linRewiring public

  -- All the remainings are defined with 'first'

  ttˢ : ∀ {_⊤} → _⊤ →ˢ `⊤
  ttˢ = first tt

  dupˢ : ∀ {A} → A →ˢ (A `× A)
  dupˢ = first dup

  <_,_>ˢ : ∀ {A B C} → (A →ˢ B) → (A →ˢ C) → A →ˢ (B `× C)
  < f , g >ˢ = dupˢ ⁏ < f × g >ˢ

  <[]>ˢ : ∀ {_⊤ A} → _⊤ →ˢ `Vec A 0
  <[]>ˢ = first <[]>

  fstˢ : ∀ {A B} → (A `× B) →ˢ A
  fstˢ = first fst

  sndˢ : ∀ {A B} → (A `× B) →ˢ B
  sndˢ = first snd

  rewireˢ : ∀ {i o} → (Fin o → Fin i) → i →ˢᵇ o
  rewireˢ f = first (rewire f)

  rewireTblˢ : ∀ {i o} → RewireTbl i o   → i →ˢᵇ o
  rewireTblˢ tbl = first (rewireTbl tbl)

  rewiringˢ : Rewiring funUˢ
  rewiringˢ = {!!}

module FunOpsˢ (funOps : FunOps funU) where

  open FunOps funOps

  forkˢ : ∀ {A B} (f g : A →ˢ B) → `Bit `× A →ˢ B
  forkˢ f g = assoc ⁏ fork f g

  -- All the remainings are defined with 'first'

  <0b>ˢ : ∀ {_⊤} → _⊤ →ˢ `Bit
  <0b>ˢ = first <0b>

  <1b>ˢ : ∀ {_⊤} → _⊤ →ˢ `Bit
  <1b>ˢ = first <1b>

  condˢ : ∀ {A} → `Bit `× A `× A →ˢ A
  condˢ = first cond

  funOpsˢ : FunOps funUˢ
  funOpsˢ = {!!}

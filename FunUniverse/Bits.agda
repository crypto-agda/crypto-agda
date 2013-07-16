{-# OPTIONS --without-K #-}
module FunUniverse.Bits where

open import Data.Nat.NP using (ℕ; _*_; module ℕ°)
open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin)
open import Function using (const; _∘′_; id)
open import Data.Vec.NP using (Vec; []; _∷_; _++_; [_]; take; drop; rewire; rewireTbl)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)

open import Data.Bit using (0b; 1b)
open import Data.Bits using (_→ᵇ_; RewireTbl)

open import FunUniverse.Data
open import FunUniverse.Core
open import FunUniverse.Category
open import FunUniverse.Rewiring.Linear

bitsFunU : FunUniverse ℕ
bitsFunU = Bits-U , _→ᵇ_

module BitsFunUniverse = FunUniverse bitsFunU
open BitsFunUniverse
open Cong-*1 _`→_
open Defaults bitsFunU

bitsFunOps : FunOps bitsFunU
bitsFunOps = mk rewiring (cond , forkᵇ) (const [ 0b ]) (const [ 1b ])
  where
  fstᵇ : ∀ {A B} → A `× B `→ A
  fstᵇ {A} = take A
  sndᵇ : ∀ {B} A → A `× B `→ B
  sndᵇ A = drop A
  <_,_>ᵇ : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  <_,_>ᵇ f g x = f x ++ g x
  forkᵇ : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B
  forkᵇ f g (b ∷ xs) = (if b then f else g) xs

  open DefaultsGroup2 id _∘′_ (const []) <_,_>ᵇ fstᵇ (λ {x} → sndᵇ x)
  open DefaultCondFromFork forkᵇ fstᵇ (λ {x} → sndᵇ x)

  cat : Category _`→_
  cat = id , _∘′_

  lin : LinRewiring bitsFunU
  lin = mk cat first (λ {x} → swap {x}) (λ {x} → assoc {x}) id id
           <_×_> (λ {x} → second {x}) id id id id

  rewiring : Rewiring bitsFunU
  rewiring = mk lin (const []) dup (const []) <_,_>ᵇ fstᵇ (λ {x} → sndᵇ x)
                (cong-*1 ∘′ rewire) (cong-*1 ∘′ rewireTbl)

bitsFunRewiring : Rewiring bitsFunU
bitsFunRewiring = FunOps.rewiring bitsFunOps

bitsFunLin : LinRewiring bitsFunU
bitsFunLin = Rewiring.linRewiring bitsFunRewiring

module BitsFunOps = FunOps bitsFunOps

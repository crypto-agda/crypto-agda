module composable where

open import Level
open import Function

record Composable {s t} {S : Set s} (_↝_ : S → S → Set t) : Set (s ⊔ t) where
  constructor mk
  infixr 1 _>>>_
  field
    _>>>_ : ∀ {A B C : S} → (A ↝ B) → (B ↝ C) → (A ↝ C)

ixFunComp : ∀ {ix s} {Ix : Set ix} (F : Ix → Set s) → Composable (λ i o → F i → F o)
ixFunComp _ = mk (λ f g x → g (f x))

funComp : ∀ {s} → Composable (λ (A B : Set s) → A → B)
funComp = ixFunComp id

opComp : ∀ {s t} {S : Set s} {_↝_ : S → S → Set t} → Composable _↝_ → Composable (flip _↝_)
opComp (mk _>>>_) = mk (flip _>>>_)

open import Data.Vec
vecFunComp : ∀ {a} (A : Set a) → Composable (λ i o → Vec A i → Vec A o)
vecFunComp A = ixFunComp (Vec A)

open import Data.Bits
bitsFunComp : Composable (λ i o → Bits i → Bits o)
bitsFunComp = ixFunComp Bits

open import Data.Unit using (⊤)

ConstArr : ∀ {a} (A : Set a) → ⊤ → ⊤ → Set a
ConstArr A _ _ = A

constComp : ∀ {a} {A : Set a} (_·_ : A → A → A) → Composable (ConstArr A)
constComp _·_ = mk _·_

-- open import Data.Fin
-- funRewireComp : Composable (λ i o → Fin o → Fin i)
-- FunRewireComp = opComp (ixFunComp Fin)

{-
open import bintree

open import Data.Nat
CircuitType : Set₁
CircuitType = (i o : ℕ) → Set

RewireTbl : CircuitType
RewireTbl i o = Vec (Fin i) o

rewireTblComp : Composable RewireTbl
rewireTblComp = {!!}
-}

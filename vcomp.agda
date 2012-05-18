module vcomp where

open import Level
open import Function

record VComposable {s t} {S : Set s} (_·_ : S → S → S) (_↝_ : S → S → Set t) : Set (s ⊔ t) where
  constructor mk
  infixr 3 _***_
  field
    _***_ : ∀ {i₀ i₁ o₀ o₁} → i₀ ↝ o₀ → i₁ ↝ o₁ → (i₀ · i₁) ↝ (o₀ · o₁)

open import Data.Nat
open import Data.Fin.NP as Fin using (Fin; inject+; raise; bound; free)

opVComp : ∀ {s t} {S : Set s} {_·_ : S → S → S} {_↝_ : S → S → Set t}
          → VComposable _·_ _↝_ → VComposable (flip _·_) (flip _↝_)
opVComp (mk _***_) = mk (flip _***_)

open import Data.Product

funComp : ∀ {s} → VComposable _×_ (λ (A B : Set s) → A → B)
funComp {s} = mk _***_ where
  _***_ : ∀ {A B C D : Set s} → (A → B) → (C → D) → A × C → B × D
  (f *** g) (x , y) = (f x , g y)

finFunVComp : VComposable _+_ (λ i o → Fin i → Fin o)
finFunVComp = mk _***_ where
  C = λ i o → Fin i → Fin o
  _***_ : ∀ {i₀ i₁ o₀ o₁} → C i₀ o₀ → C i₁ o₁ → C (i₀ + i₁) (o₀ + o₁)
  _***_ {i}      f g x with Fin.cmp i _ x
  _***_          f _ ._ | Fin.bound x = inject+ _ (f x)
  _***_ {o₀ = o} _ g ._ | Fin.free  x = raise o (g x)

-- finFunOpVComp = opVComp finFunVComp [modulo commutativity of _+_]
finFunOpVComp : VComposable _+_ (λ i o → Fin o → Fin i)
finFunOpVComp = mk _***_ where
  C = λ i o → Fin o → Fin i
  _***_ : ∀ {i₀ i₁ o₀ o₁} → C i₀ o₀ → C i₁ o₁ → C (i₀ + i₁) (o₀ + o₁)
  _***_ {o₀ = o} f g x with Fin.cmp o _ x
  _***_          f _ ._ | Fin.bound x = inject+ _ (f x)
  _***_ {i}      _ g ._ | Fin.free  x = raise i (g x)

open import Data.Vec

vecFunVComp : ∀ {a} (A : Set a) → VComposable _+_ (λ i o → Vec A i → Vec A o)
vecFunVComp A = mk _***_ where
  C = λ i o → Vec A i → Vec A o
  _***_ : ∀ {i₀ i₁ o₀ o₁} → C i₀ o₀ → C i₁ o₁ → C (i₀ + i₁) (o₀ + o₁)
  (f *** g) xs with splitAt _ xs
  ... | ys , zs , _ = f ys ++ g zs

open import Data.Unit using (⊤)
open import composable using (ConstArr)

constVComp : ∀ {a} {A : Set a} (_***_ : A → A → A) → VComposable _ (ConstArr A)
constVComp _***_ = mk _***_

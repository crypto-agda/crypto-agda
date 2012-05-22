module vcomp where

open import Level
open import Function
open import Data.Unit using (⊤)
open import composable using (ConstArr)

VComposition : ∀ {i j} {I : Set i} (_×_ : I → I → I) (_↝_ : I → I → Set j) → Set (i ⊔ j)
VComposition _×_ _↝_ = ∀ {i₀ i₁ o₀ o₁} → i₀ ↝ o₀ → i₁ ↝ o₁ → (i₀ × i₁) ↝ (o₀ × o₁)

VCIComposition : ∀ {i t a} {I : Set i} {T : Set t}
                   (_×ᵢ_ : I → I → I)
                   (_×_ : T → T → T)
                   (⟨_⟩_↝_ : I → T → T → Set a) → Set (a ⊔ t ⊔ i)
VCIComposition _×ᵢ_ _×_ ⟨_⟩_↝_ =
  ∀ {j₀ j₁ i₀ i₁ o₀ o₁} → ⟨ j₀ ⟩ i₀ ↝ o₀ → ⟨ j₁ ⟩ i₁ ↝ o₁ → ⟨ j₀ ×ᵢ j₁ ⟩ (i₀ × i₁) ↝ (o₀ × o₁)

record VIComposable {i j t a} {I : Set i} {_×ᵢ_ : I → I → I} {_↝ᵢ_ : I → I → Set j} {T : I → Set t}
                    (_·_ : VComposition _×ᵢ_ _↝ᵢ_)
                    (_×_ : ∀ {i₀ i₁} → T i₀ → T i₁ → T (i₀ ×ᵢ i₁))
                    (⟨_⟩_↝_ : ∀ {i₀ i₁} → i₀ ↝ᵢ i₁ → T i₀ → T i₁ → Set a) : Set (a ⊔ t ⊔ i ⊔ j) where
  constructor mk
  infixr 3 _***_
  field
    _***_ : ∀ {i₀ i₁ o₀ o₁} {j₀ : i₀ ↝ᵢ o₀} {j₁ : i₁ ↝ᵢ o₁} {A B C D}
            → ⟨ j₀ ⟩ A ↝ C → ⟨ j₁ ⟩ B ↝ D
            → ⟨ j₀ · j₁ ⟩ (A × B) ↝ (C × D)

vComposition : ∀ {t a} {T : Set t} {_×_ : T → T → T} {_↝_ : T → T → Set a}
               → VIComposable {I = ⊤} {_↝ᵢ_ = λ _ _ → ⊤} {T = const T} _ _×_ (const _↝_)
               → VComposition _×_ _↝_
vComposition (mk _***_) = _***_

vCIComposition : ∀ {i t a} {T : Set t} {_×_ : T → T → T}
                 {I : Set i} {_·_ : I → I → I}
                 {⟨_⟩_↝_ : I → T → T → Set a}
               → VIComposable {I = ⊤} _·_ _×_ ⟨_⟩_↝_
               → VCIComposition _·_ _×_ ⟨_⟩_↝_
vCIComposition (mk _***_) = _***_

VComposable : ∀ {t a} {T : Set t} (_×_ : T → T → T) (_↝_ : T → T → Set a) → Set (t ⊔ a)
VComposable _×_ _↝_ = VIComposable {i = zero} {_↝ᵢ_ = ConstArr ⊤} _ _×_ (const _↝_)

{- VComposable unfolds to:
record VComposable {t a} {T : Set t} (_·_ : T → T → T) (_↝_ : T → T → Set a) : Set (t ⊔ a) where
  constructor mk
  infixr 3 _***_
  field
    _***_ : ∀ {i₀ i₁ o₀ o₁} → i₀ ↝ o₀ → i₁ ↝ o₁ → (i₀ · i₁) ↝ (o₀ · o₁)
-}

module VComposable = VIComposable

open import Data.Nat
open import Data.Fin.NP as Fin using (Fin; inject+; raise; bound; free)

opVComp : ∀ {t a} {T : Set t} {_×_ : T → T → T} {_↝_ : T → T → Set a}
          → VComposable _×_ _↝_ → VComposable (flip _×_) (flip _↝_)
opVComp (mk _***_) = mk (flip _***_)

open import Data.Product

funVComp : ∀ {t} → VComposable _×_ (λ (A B : Set t) → A → B)
funVComp {t} = mk _***_ where
  _***_ : ∀ {A B C D : Set t} → (A → B) → (C → D) → A × C → B × D
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

constVComp : ∀ {a} {A : Set a} (_***_ : A → A → A) → VComposable _ (ConstArr A)
constVComp _***_ = mk _***_

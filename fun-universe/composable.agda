module composable where

open import Level
open import Function
open import Data.Unit using (⊤)
open import Relation.Binary

Arrow : ∀ {i} → Set i → ∀ j → Set (suc j ⊔ i)
Arrow = Rel

Composition : ∀ {a ℓ} {A : Set a} → Arrow A ℓ → Set _
Composition = Transitive

Identity : ∀ {a ℓ} {A : Set a} → Arrow A ℓ → Set _
Identity = Reflexive

IArrow : ∀ {i j t} {I : Set i} (_↝ᵢ_ : Arrow I j) (T : I → Set t) a → Set _
IArrow _↝ᵢ_ T a = ∀ {i₀ i₁} → i₀ ↝ᵢ i₁ → T i₀ → T i₁ → Set a

IReflexivity : ∀ {a i j t} {I : Set i} {R : Rel I j} {T : I → Set t} → Reflexive R → IArrow R T a → Set _
IReflexivity R-refl Arr = ∀ {i A} → Arr (R-refl {i}) A A

IIdentity : ∀ {a i j t} {I : Set i} {_↝ᵢ_ : Arrow I j} {T : I → Set t} → Identity _↝ᵢ_ → IArrow _↝ᵢ_ T a → Set _
IIdentity = IReflexivity

ITrans : ∀ {i j t a} {I : Set i} {R₀ R₁ R₂ : Rel I j} {T : I → Set t}
           (R-trans : Trans R₀ R₁ R₂)
           (Arr₀ : IArrow R₀ T a)
           (Arr₀ : IArrow R₁ T a)
           (Arr₀ : IArrow R₂ T a)
         → Set _
ITrans R-trans Arr₀ Arr₁ Arr₂
  = ∀ {i₀ i₁ i₂ j₀ j₁} → Trans (Arr₀ j₀) (Arr₁ j₁) (Arr₂ (R-trans {i₀} {i₁} {i₂} j₀ j₁))

ITransitive : ∀ {i j t a} {I : Set i} {R : Rel I j} {T : I → Set t}
                → Transitive R → IArrow R T a → Set _
ITransitive {R = R} R-trans Arr = ITrans {R₀ = R} {R} {R} R-trans Arr Arr Arr

IComposition : ∀ {i j t a} {I : Set i} {_↝ᵢ_ : Arrow I j} {T : I → Set t}
                   (_·_ : Composition _↝ᵢ_)
                   (⟨_⟩_↝_ : IArrow _↝ᵢ_ T a) → Set _
IComposition = ITransitive

record IComposable {i j t a} {I : Set i} {_↝ᵢ_ : Arrow I j} {T : I → Set t}
                   (_·_ : Composition _↝ᵢ_)
                   (⟨_⟩_↝_ : IArrow _↝ᵢ_ T a)
                 : Set (a ⊔ t ⊔ i ⊔ j) where
  constructor mk
  infixr 1 _>>>_
  field
--    _>>>_ : ∀ {i₀ i₁ i₂} {ix₀ : i₀ ↝ᵢ i₁} {ix₁ : i₁ ↝ᵢ i₂} {A B C}
--            → (⟨ ix₀ ⟩ A ↝ B) → (⟨ ix₁ ⟩ B ↝ C) → (⟨ ix₀ · ix₁ ⟩ A ↝ C)
    _>>>_ : IComposition (λ {η} → _·_ {η}) ⟨_⟩_↝_

open import Relation.Binary.PropositionalEquality
Refl-Unit : ∀ {ℓ a} {A : Set a} {R : Rel A ℓ} → Reflexive R → Transitive R → Set _
Refl-Unit {R = R} R-refl R-trans = ∀ {x y} (p : R x y) → R-trans R-refl p ≡ p

{-
record ICat        {i j t a} {I : Set i} {_↝ᵢ_ : Arrow I j} {T : I → Set t}
                   {_·_ : Composition _↝ᵢ_}
                   {⟨_⟩_↝_ : IArrow a _↝ᵢ_ T}
                   (comp : IComposable _·_ ⟨_⟩_↝_)
                   {idᵢ : Identity _↝ᵢ_}
                   (id : IIdentity (λ {η} → idᵢ {η}) ⟨_⟩_↝_)
                   (_≈ᵢ_ : ∀ {a b} (i j : a ↝ᵢ b) → Set)
                   (_≈_ : ∀ {i j A B} → i ≈ᵢ j → ⟨ i ⟩ A ↝ B → ⟨ j ⟩ A ↝ B → Set) : Set
          where
  constructor mk
  open IComposable comp
  field
    id-unit->>> :
      ∀ f → ⟨ id >>> f ≈ f
-}
open import Data.Unit using (⊤)

ConstArr : ∀ {a} (A : Set a) → ⊤ → ⊤ → Set a
ConstArr A _ _ = A

Composable : ∀ {t a} {T : Set t} (_↝_ : T → T → Set a) → Set (t ⊔ a)
Composable _↝_ = IComposable {i = zero} {_↝ᵢ_ = ConstArr ⊤} _ (const _↝_)

{- Composable, unfolded:
record Composable {t a} {T : Set t} (_↝_ : T → T → Set a) : Set (t ⊔ a) where
  constructor mk
  infixr 1 _>>>_
  field
    _>>>_ : ∀ {A B C} → (A ↝ B) → (B ↝ C) → (A ↝ C)
-}

constComp' : ∀ {a} {A : Set a} (_·_ : A → A → A) → Composition (ConstArr A)
constComp' _·_ = _·_

constComp : ∀ {a} {A : Set a} (_·_ : A → A → A) → Composable (ConstArr A)
constComp _·_ = mk _·_

module Composable = IComposable

ixFunComp : ∀ {ix t} {Ix : Set ix} (F : Ix → Set t) → Composable (λ i o → F i → F o)
ixFunComp _ = mk (λ f g x → g (f x))

funComp : ∀ {t} → Composable (λ (A B : Set t) → A → B)
funComp = ixFunComp id

opComp : ∀ {t a} {T : Set t} {_↝_ : T → T → Set a} → Composable _↝_ → Composable (flip _↝_)
opComp (mk _>>>_) = mk (flip _>>>_)

open import Data.Vec
vecFunComp : ∀ {a} (A : Set a) → Composable (λ i o → Vec A i → Vec A o)
vecFunComp A = ixFunComp (Vec A)

open import Data.Bits
bitsFunComp : Composable (λ i o → Bits i → Bits o)
bitsFunComp = ixFunComp Bits

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

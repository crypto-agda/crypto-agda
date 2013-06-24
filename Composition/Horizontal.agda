module Composition.Horizontal where

open import Level
open import Type hiding (★)
open import Function
open import Relation.Binary

Arrow : ∀ {i} → ★ i → ∀ j → ★ (suc j ⊔ i)
Arrow = Rel

HComposition : ∀ {a ℓ} {A : ★ a} → Arrow A ℓ → ★ _
HComposition = Transitive

Identity : ∀ {a ℓ} {A : ★ a} → Arrow A ℓ → ★ _
Identity = Reflexive

IArrow : ∀ {i j t} {I : ★ i} (_↝ᵢ_ : Arrow I j) (T : I → ★ t) a → ★ _
IArrow _↝ᵢ_ T a = ∀ {i₀ i₁} → i₀ ↝ᵢ i₁ → T i₀ → T i₁ → ★ a

IReflexivity : ∀ {a i j t} {I : ★ i} {R : Rel I j} {T : I → ★ t} → Reflexive R → IArrow R T a → ★ _
IReflexivity R-refl Arr = ∀ {i A} → Arr (R-refl {i}) A A

IIdentity : ∀ {a i j t} {I : ★ i} {_↝ᵢ_ : Arrow I j} {T : I → ★ t} → Identity _↝ᵢ_ → IArrow _↝ᵢ_ T a → ★ _
IIdentity = IReflexivity

ITrans : ∀ {i j t a} {I : ★ i}
           {R₀ R₁ R₂ : Rel I j}
           {T : I → ★ t}
           (R-trans : Trans R₀ R₁ R₂)
           (Arr₀ : IArrow R₀ T a)
           (Arr₀ : IArrow R₁ T a)
           (Arr₀ : IArrow R₂ T a)
         → ★ _
ITrans R-trans Arr₀ Arr₁ Arr₂
  = ∀ {i₀ i₁ i₂ j₀ j₁} → Trans (Arr₀ j₀) (Arr₁ j₁)
                           (Arr₂ (R-trans {i₀} {i₁} {i₂} j₀ j₁))

ITransitive : ∀ {i j t a} {I : ★ i} {R : Rel I j}
                {T : I → ★ t}
              → Transitive R → IArrow R T a → ★ _
ITransitive {R = R} R-trans Arr
  = ITrans {R₀ = R} R-trans Arr Arr Arr

IHComposition : ∀ {i j t a} {I : ★ i}
                 {_↝ᵢ_ : Arrow I j} {T : I → ★ t}
                 (_·_ : HComposition _↝ᵢ_)
                 (⟨_⟩_↝_ : IArrow _↝ᵢ_ T a) → ★ _
IHComposition = ITransitive

record IHComposable {i j t a} {I : ★ i}
                    {_↝ᵢ_ : Arrow I j} {T : I → ★ t}
                    (_·_ : HComposition _↝ᵢ_)
                    (⟨_⟩_↝_ : IArrow _↝ᵢ_ T a)
                  : ★ (a ⊔ t ⊔ i ⊔ j) where
  constructor mk
  infixr 1 _>>>_
  field
    _>>>_ : IHComposition (λ {η} → _·_ {η}) ⟨_⟩_↝_

open import Relation.Binary.PropositionalEquality
Refl-Unit : ∀ {ℓ a} {A : ★ a} {R : Rel A ℓ} → Reflexive R → Transitive R → ★ _
Refl-Unit {R = R} R-refl R-trans = ∀ {x y} (p : R x y) → R-trans R-refl p ≡ p

open import Data.One using (𝟙)
ConstArr : ∀ {a} (A : ★ a) → 𝟙 → 𝟙 → ★ a
ConstArr A _ _ = A

HComposable : ∀ {t a} {T : ★ t} (_↝_ : T → T → ★ a) → ★ (t ⊔ a)
HComposable _↝_ = IHComposable {i = zero} {_↝ᵢ_ = ConstArr 𝟙} _ (const _↝_)

{- Composable, unfolded:
record HComposable {t a} {T : ★ t} (_↝_ : T → T → ★ a) : ★ (t ⊔ a) where
  constructor mk
  infixr 1 _>>>_
  field
    _>>>_ : ∀ {A B C} → (A ↝ B) → (B ↝ C) → (A ↝ C)
-}

constHComp' : ∀ {a} {A : ★ a} (_·_ : A → A → A) → HComposition (ConstArr A)
constHComp' _·_ = _·_

constHComp : ∀ {a} {A : ★ a} (_·_ : A → A → A) → HComposable (ConstArr A)
constHComp _·_ = mk _·_

module HComposable = IHComposable

ixFunHComp : ∀ {ix t} {Ix : ★ ix} (F : Ix → ★ t) → HComposable (λ i o → F i → F o)
ixFunHComp _ = mk (λ f g x → g (f x))

funHComp : ∀ {t} → HComposable (λ (A B : ★ t) → A → B)
funHComp = ixFunHComp id

opHComp : ∀ {t a} {T : ★ t} {_↝_ : T → T → ★ a} → HComposable _↝_ → HComposable (flip _↝_)
opHComp (mk _>>>_) = mk (flip _>>>_)

module _ {a} (A : ★ a) where
    open import Data.Vec.NP
    open FunVec {A = A}
    vecFunHComp : HComposable _→ᵛ_
    vecFunHComp = ixFunHComp (Vec A)

open import Data.Bits
bitsFunHComp : HComposable _→ᵇ_
bitsFunHComp = ixFunHComp Bits

module powered-flat-funs where

open import Data.Nat
open import Data.Unit using (⊤)
import Level as L
open import flat-funs
open import composable
open import vcomp
open import ann

record PowerOps (Power : Set) : Set where
  constructor mk
  infixr 1 _>>>ᵖ_
  infixr 3 _***ᵖ_
  field
    idᵖ : Power
    _>>>ᵖ_ _***ᵖ_ : Power → Power → Power

constPowerOps : PowerOps ⊤
constPowerOps = _

record PoweredFlatFuns (Power : Set) {t} (T : Set t) : Set (L.suc t) where
  constructor mk
  field
    `Bits   : ℕ → T
    `Bit    : T
    _`×_    : T → T → T
    ⟨_⟩_↝_  : Power → T → T → Set
  infixr 2 _`×_
  infix 0 ⟨_⟩_↝_

⊤-poweredFlatFuns : ∀ {t} {T : Set t} → FlatFuns T → PoweredFlatFuns ⊤ T
⊤-poweredFlatFuns ff = mk `Bits `Bit _`×_ (λ _ A B → A `→ B) where open FlatFuns ff

record PoweredFlatFunsOps {P t} {T : Set t} (powerOps : PowerOps P) (♭Funs : PoweredFlatFuns P T) : Set t where
  constructor mk
  open PoweredFlatFuns ♭Funs
  open PowerOps powerOps
  field
    idO : ∀ {A p} → ⟨ p ⟩ A ↝ A
    isIComposable  : IComposable  {I = ⊤} _>>>ᵖ_ ⟨_⟩_↝_
    isVIComposable : VIComposable {I = ⊤} _***ᵖ_ _`×_ ⟨_⟩_↝_
  open PoweredFlatFuns ♭Funs public
  open PowerOps powerOps public
  open IComposable isIComposable public
  open VIComposable isVIComposable public

⊤-poweredFlatFunsOps : ∀ {t} {T : Set t} {♭Funs : FlatFuns T}
                 → FlatFunsOps ♭Funs → PoweredFlatFunsOps _ (⊤-poweredFlatFuns ♭Funs)
⊤-poweredFlatFunsOps ops = mk idO isComposable isVComposable where open FlatFunsOps ops

poweredFlatFuns : ∀ {t} {T : Set t} {P}
                   → FlatFuns T → PoweredFlatFuns P T
poweredFlatFuns ff = mk `Bits `Bit _`×_ (λ p A B → Ann p (A `→ B)) where open FlatFuns ff

poweredFlatFunsOps : ∀ {t} {T : Set t} {P} (funPowerOps : PowerOps P)
                    {♭Funs : FlatFuns T}
                    → FlatFunsOps ♭Funs → PoweredFlatFunsOps funPowerOps (poweredFlatFuns ♭Funs)
poweredFlatFunsOps funPowerOps {♭Funs} (mk idO (mk _>>>_) (mk _***_) _)
   = mk (mk idO) (mk (λ x y → mk (get x >>> get y))) (mk (λ x y → mk (get x *** get y)))
      where open Ann

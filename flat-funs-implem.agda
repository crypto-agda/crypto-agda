module flat-funs-implem where

open import Data.Unit using (⊤)
open import Data.Fin using (Fin)
open import Data.Nat.NP using (ℕ)
open import Data.Bool using (if_then_else_)
import Data.Vec.NP as V
import Function as F
import Data.Product as ×
open F using (const; _∘′_)
open V using (Vec; []; _∷_; _++_; [_])
open × using (_×_; _,_; proj₁; proj₂; uncurry)

open import Data.Bits using (_→ᵇ_; 0b; 1b)

open import data-universe
open import flat-funs

-→- : Set → Set → Set
-→- A B = A → B

_→ᶠ_ : ℕ → ℕ → Set
_→ᶠ_ i o = Fin i → Fin o

agdaFunU : FunUniverse Set
agdaFunU = mk Set-U -→-

module AgdaFunUniverse = FunUniverse agdaFunU

bitsFunU : FunUniverse ℕ
bitsFunU = mk Bits-U _→ᵇ_

module BitsFunUniverse = FunUniverse bitsFunU

finFunU : FunUniverse ℕ
finFunU = mk Fin-U _→ᶠ_

module FinFunUniverse = FunUniverse finFunU

funLin : LinRewiring agdaFunU
funLin = mk F.id _∘′_
            (λ f → ×.map f F.id)
            ×.swap (λ {((x , y) , z) → x , (y , z) }) (λ x → _ , x) proj₂
            (λ f g → ×.map f g) (λ f → ×.map F.id f)
            (F.const []) _ (uncurry _∷_) V.uncons

funRewiring : Rewiring agdaFunU
funRewiring = mk funLin _ (λ x → x , x) (F.const []) ×.<_,_> proj₁ proj₂

agdaFunOps : FunOps agdaFunU
agdaFunOps = mk funRewiring (F.const 0b) (F.const 1b) (λ { (b , x , y) → if b then x else y })
             (λ { f g (b , x) → (if b then f else g) x })

module AgdaFunOps = FunOps agdaFunOps

bitsFunOps : FunOps bitsFunU
bitsFunOps = mk rewiring (const [ 0b ]) (const [ 1b ]) cond forkᵇ
  where
  open BitsFunUniverse
  open AgdaFunOps using (id; _∘_)
  fstᵇ : ∀ {A B} → A `× B `→ A
  fstᵇ {A} = V.take A
  sndᵇ : ∀ {B} A → A `× B `→ B
  sndᵇ A = V.drop A
  <_,_>ᵇ : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  <_,_>ᵇ f g x = f x ++ g x
  forkᵇ : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B
  forkᵇ f g (b ∷ xs) = (if b then f else g) xs
  open Defaults bitsFunU
  open DefaultsGroup2 id _∘_ (const []) <_,_>ᵇ fstᵇ (λ {x} → sndᵇ x)
  open DefaultCond forkᵇ fstᵇ (λ {x} → sndᵇ x)

  lin : LinRewiring bitsFunU
  lin = mk id _∘_ first (λ {x} → swap {x}) (λ {x} → assoc {x}) id id
           <_×_> (λ {x} → second {x}) id id id id

  rewiring : Rewiring bitsFunU
  rewiring = mk lin (const []) dup (const []) <_,_>ᵇ fstᵇ (λ {x} → sndᵇ x)

bitsFunRewiring : Rewiring bitsFunU
bitsFunRewiring = FunOps.rewiring bitsFunOps

bitsFunLin : LinRewiring bitsFunU
bitsFunLin = Rewiring.linRewiring bitsFunRewiring

module BitsFunOps = FunOps bitsFunOps

constFuns : Set → FunUniverse ⊤
constFuns A = mk ⊤-U (λ _ _ → A)

module ConstFunTypes A = FunUniverse (constFuns A)

⊤-FunOps : FunOps (constFuns ⊤)
⊤-FunOps = _

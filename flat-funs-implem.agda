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

fun♭Funs : FlatFuns Set
fun♭Funs = mk Set-U -→-

module FunTypes = FlatFuns fun♭Funs

bitsFun♭Funs : FlatFuns ℕ
bitsFun♭Funs = mk Bits-U _→ᵇ_

module BitsFunTypes = FlatFuns bitsFun♭Funs

finFun♭Funs : FlatFuns ℕ
finFun♭Funs = mk Fin-U _→ᶠ_

module FinFunTypes = FlatFuns finFun♭Funs

fun♭Ops : FlatFunsOps fun♭Funs
fun♭Ops = mk F.id _∘′_
             (F.const 0b) (F.const 1b) (λ { (b , x , y) → if b then x else y })
             (λ { f g (b , x) → (if b then f else g) x }) _
             ×.<_,_> proj₁ proj₂ (λ x → x , x) (λ f → ×.map f F.id)
             ×.swap (λ {((x , y) , z) → x , (y , z) }) (λ x → _ , x) proj₂
             (λ f g → ×.map f g) (λ f → ×.map F.id f)
             (F.const []) (uncurry _∷_) V.uncons

module FunOps = FlatFunsOps fun♭Ops

bitsFun♭Ops : FlatFunsOps bitsFun♭Funs
bitsFun♭Ops = mk id _∘_
                 (const [ 0b ]) (const [ 1b ]) cond forkᵇ (const [])
                 <_,_>ᵇ fstᵇ (λ {x} → sndᵇ x) dup first
                 (λ {x} → swap {x}) (λ {x} → assoc {x}) id id
                 <_×_> (λ {x} → second {x}) (const []) id id
  where
  open BitsFunTypes
  open FunOps using (id; _∘_)
  fstᵇ : ∀ {A B} → A `× B `→ A
  fstᵇ {A} = V.take A
  sndᵇ : ∀ {B} A → A `× B `→ B
  sndᵇ A = V.drop A
  <_,_>ᵇ : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  <_,_>ᵇ f g x = f x ++ g x
  forkᵇ : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B
  forkᵇ f g (b ∷ xs) = (if b then f else g) xs
  open Defaults bitsFun♭Funs
  open DefaultsGroup2 id _∘_ (const []) <_,_>ᵇ fstᵇ (λ {x} → sndᵇ x)
  open DefaultCond forkᵇ fstᵇ (λ {x} → sndᵇ x)

module BitsFunOps = FlatFunsOps bitsFun♭Ops

constFuns : Set → FlatFuns ⊤
constFuns A = mk ⊤-U (λ _ _ → A)

module ConstFunTypes A = FlatFuns (constFuns A)

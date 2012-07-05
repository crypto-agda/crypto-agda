module bits-fun-universe where

open import Data.Nat.NP using (ℕ; _*_; module ℕ°)
open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin)
import Data.Vec.NP as V
import Function as F
import Data.Product as ×
open F using (const; _∘′_)
open V using (Vec; []; _∷_; _++_; [_])
open × using (_×_; _,_; proj₁; proj₂; uncurry)

open import Data.Bits using (_→ᵇ_; 0b; 1b; RewireTbl)

open import data-universe
open import fun-universe

bitsFunU : FunUniverse ℕ
bitsFunU = mk Bits-U _→ᵇ_

module BitsFunUniverse = FunUniverse bitsFunU

bitsFunOps : FunOps bitsFunU
bitsFunOps = mk rewiring (const [ 0b ]) (const [ 1b ]) cond forkᵇ
  where
  open BitsFunUniverse
  open F using (id; _∘′_)
  fstᵇ : ∀ {A B} → A `× B `→ A
  fstᵇ {A} = V.take A
  sndᵇ : ∀ {B} A → A `× B `→ B
  sndᵇ A = V.drop A
  <_,_>ᵇ : ∀ {A B C} → (A `→ B) → (A `→ C) → A `→ B `× C
  <_,_>ᵇ f g x = f x ++ g x
  forkᵇ : ∀ {A B} (f g : A `→ B) → `Bit `× A `→ B
  forkᵇ f g (b ∷ xs) = (if b then f else g) xs

  cong-*1 : ∀ {i o} → i `→ o → (i * 1) `→ (o * 1)
  cong-*1 {i} {o} rewrite proj₂ ℕ°.*-identity i
                        | proj₂ ℕ°.*-identity o = id

  open Defaults bitsFunU
  open DefaultsGroup2 id _∘′_ (const []) <_,_>ᵇ fstᵇ (λ {x} → sndᵇ x)
  open DefaultCond forkᵇ fstᵇ (λ {x} → sndᵇ x)

  lin : LinRewiring bitsFunU
  lin = mk id _∘′_ first (λ {x} → swap {x}) (λ {x} → assoc {x}) id id
           <_×_> (λ {x} → second {x}) id id id id

  rewiring : Rewiring bitsFunU
  rewiring = mk lin (const []) dup (const []) <_,_>ᵇ fstᵇ (λ {x} → sndᵇ x)
                (cong-*1 ∘′ V.rewire) (cong-*1 ∘′ V.rewireTbl)

bitsFunRewiring : Rewiring bitsFunU
bitsFunRewiring = FunOps.rewiring bitsFunOps

bitsFunLin : LinRewiring bitsFunU
bitsFunLin = Rewiring.linRewiring bitsFunRewiring

module BitsFunOps = FunOps bitsFunOps

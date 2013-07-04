module FunUniverse.Agda where

open import Type
open import Data.Two using (proj′)
import Data.Vec.NP as V
import Function as F
import Data.Product as ×
open F using (const; _∘′_)
open V using ([]; _∷_)
open × using (_×_; _,_; proj₁; proj₂; uncurry)

open import Data.Bit using (0b; 1b)

open import FunUniverse.Data
open import FunUniverse.Category
open import FunUniverse.Rewiring.Linear
open import FunUniverse.Core

-→- : ★ → ★ → ★
-→- A B = A → B

agdaFunU : FunUniverse ★
agdaFunU = ★-U , -→-

module AgdaFunUniverse = FunUniverse agdaFunU

funCat : Category -→-
funCat = F.id , _∘′_

funLin : LinRewiring agdaFunU
funLin = mk funCat
            (λ f → ×.map f F.id)
            ×.swap (λ {((x , y) , z) → x , (y , z) }) (λ x → _ , x) proj₂
            (λ f g → ×.map f g) (λ f → ×.map F.id f)
            (F.const []) _ (uncurry _∷_) V.uncons

funRewiring : Rewiring agdaFunU
funRewiring = mk funLin _ (λ x → x , x) (F.const []) ×.<_,_> proj₁ proj₂
                 V.rewire V.rewireTbl

funFork : HasFork agdaFunU
funFork = (λ { (b , xy)    → proj′ xy b })
        , (λ { f g (b , x) → proj′ (f , g) b x })

agdaFunOps : FunOps agdaFunU
agdaFunOps = mk funRewiring funFork (F.const 0b) (F.const 1b)

module AgdaFunOps = FunOps agdaFunOps

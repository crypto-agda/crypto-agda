module agda-fun-universe where

open import Type
open import Data.Bool using (if_then_else_)
import Data.Vec.NP as V
import Function as F
import Data.Product as ×
open F using (const; _∘′_)
open V using ([]; _∷_)
open × using (_×_; _,_; proj₁; proj₂; uncurry)

open import Data.Bits using (0b; 1b)

open import data-universe
open import fun-universe

-→- : ★ → ★ → ★
-→- A B = A → B

agdaFunU : FunUniverse ★
agdaFunU = ★-U , -→-

module AgdaFunUniverse = FunUniverse agdaFunU

funLin : LinRewiring agdaFunU
funLin = mk F.id _∘′_
            (λ f → ×.map f F.id)
            ×.swap (λ {((x , y) , z) → x , (y , z) }) (λ x → _ , x) proj₂
            (λ f g → ×.map f g) (λ f → ×.map F.id f)
            (F.const []) _ (uncurry _∷_) V.uncons

funRewiring : Rewiring agdaFunU
funRewiring = mk funLin _ (λ x → x , x) (F.const []) ×.<_,_> proj₁ proj₂
                 V.rewire V.rewireTbl

funFork : HasFork agdaFunU
funFork = (λ { (b , x , y) → if b then x else y })
        , (λ { f g (b , x) → (if b then f else g) x })

agdaFunOps : FunOps agdaFunU
agdaFunOps = mk funRewiring funFork (F.const 0b) (F.const 1b)

module AgdaFunOps = FunOps agdaFunOps

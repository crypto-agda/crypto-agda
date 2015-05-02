{-# OPTIONS --without-K #-}
module FunUniverse.Agda where

open import Type
open import Data.Two using (proj′)
import Data.Vec.NP as V
import Function as F
import Data.Product.NP as ×
open F using (const; _∘′_)
open V using ([]; _∷_)
open × using (_×_; _,_; fst; snd; uncurry; Δ)

open import Data.One using (𝟙)
open import Data.Two using (𝟚)
open import Data.Vec using (Vec)
open import Data.Bit using (0b; 1b)

open import FunUniverse.Data
open import FunUniverse.Category
open import FunUniverse.Rewiring.Linear
open import FunUniverse.Core

-→- : ★ → ★ → ★
-→- A B = A → B

funCat : Category -→-
funCat = F.id , _∘′_

module Abstract𝟚 (some𝟚 : ★) where

    private
        ★-U' : Universe ★₀
        ★-U' = mk 𝟙 some𝟚 _×_ Vec

    agdaFunU : FunUniverse ★
    agdaFunU = ★-U' , -→-

    module AgdaFunUniverse = FunUniverse agdaFunU
 
    funLin : LinRewiring agdaFunU
    funLin = record
               { cat = funCat
               ; first = ×.first
               ; swap = ×.swap
               ; assoc = λ {((x , y) , z) → x , (y , z) }
               ; <tt,id> = λ x → _ , x
               ; snd<tt,> = snd
               ; <_×_> = λ f g → ×.map f g
               ; second = ×.second′
               ; tt→[] = F.const []
               ; []→tt = _
               ; <∷> = uncurry _∷_
               ; uncons = V.uncons
               }

    funRewiring : Rewiring agdaFunU
    funRewiring = record
                    { linRewiring = funLin
                    ; tt = _
                    ; dup = Δ
                    ; <[]> = F.const []
                    ; <_,_> = ×.<_,_>
                    ; fst = fst
                    ; snd = snd
                    ; rewire = V.rewire
                    ; rewireTbl = V.rewireTbl
                    }

open Abstract𝟚 𝟚 public

funFork : HasFork agdaFunU
funFork = (λ { (b , xy)    → proj′ xy b })
        , (λ { f g (b , x) → proj′ (f , g) b x })

agdaFunOps : FunOps agdaFunU
agdaFunOps = record { rewiring = funRewiring ; hasFork = funFork ; <0₂> = F.const 0b ; <1₂> = F.const 1b }

module AgdaFunOps = FunOps agdaFunOps
-- -}

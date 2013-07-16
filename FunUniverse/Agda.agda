{-# OPTIONS --without-K #-}
module FunUniverse.Agda where

open import Type
open import Data.Two using (proj′)
import Data.Vec.NP as V
import Function as F
import Data.Product as ×
open F using (const; _∘′_)
open V using ([]; _∷_)
open × using (_×_; _,_; proj₁; proj₂; uncurry)

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
    funLin = mk funCat
                (λ f → ×.map f F.id)
                ×.swap (λ {((x , y) , z) → x , (y , z) }) (λ x → _ , x) proj₂
                (λ f g → ×.map f g) (λ f → ×.map F.id f)
                (F.const []) _ (uncurry _∷_) V.uncons

    funRewiring : Rewiring agdaFunU
    funRewiring = mk funLin _ (λ x → x , x) (F.const []) ×.<_,_> proj₁ proj₂
                     V.rewire V.rewireTbl

open Abstract𝟚 𝟚 public

funFork : HasFork agdaFunU
funFork = (λ { (b , xy)    → proj′ xy b })
        , (λ { f g (b , x) → proj′ (f , g) b x })

agdaFunOps : FunOps agdaFunU
agdaFunOps = mk funRewiring funFork (F.const 0b) (F.const 1b)

module AgdaFunOps = FunOps agdaFunOps

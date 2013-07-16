{-# OPTIONS --without-K #-}
open import Type
open import Data.Nat.NP
open import Data.Bool using (if_then_else_)
import Data.Vec as V
open V using (Vec; []; _∷_)
open import Function.NP hiding (id)
open import FunUniverse.Core hiding (_,_)
open import Data.Fin using (Fin; zero; suc; #_; inject+; raise) renaming (toℕ to Fin▹ℕ)

module adder where

module FunAdder
  {t}
  {T : ★_ t}
  {funU : FunUniverse T}
  (funOps : FunOps funU)
  where

    open FunUniverse funU
    open FunOps funOps renaming (_∘_ to _`∘_)


    --iter : ∀ {n A B S} → (S `× A `→ S `× B) → S `× `Vec A n `→ `Vec B n

    msb-adder : ∀ {n} → `Bits n `× `Bits n `→ `Bits n
    msb-adder = <tt⁏ <0₂> , zip > ⁏ mapAccum full-adder ⁏ snd

    -- TODO reverses all over the places... switch to lsb first?
    -- lsb
    adder : ∀ {n} → `Bits n `× `Bits n `→ `Bits n
    adder = < reverse × reverse > ⁏ msb-adder ⁏ reverse

    open import Data.Digit

    ℕ▹`Bits : ∀ ℓ → ℕ → `𝟙 `→ `Bits ℓ
    ℕ▹`Bits ℓ n₀ = constBits (V.reverse (L▹V (L.map F▹𝟚 (proj₁ (toDigits 2 n₀)))))
      where open import Data.List as L
            open import Data.Product
            open import Data.Two
            L▹V : ∀ {n} → List 𝟚 → Vec 𝟚 n
            L▹V {zero} xs = []
            L▹V {suc n} [] = V.replicate 0₂
            L▹V {suc n} (x ∷ xs) = x ∷ L▹V xs
            F▹𝟚 : Fin 2 → 𝟚
            F▹𝟚 zero    = 0₂
            F▹𝟚 (suc _) = 1₂

{-
open import IO
import IO.Primitive
-}
open import Data.One
open import Data.Two
open import Data.Product
--open import Coinduction
open import FunUniverse.Agda
--open import Data.Nat.Show
open FunAdder agdaFunOps
open FunOps agdaFunOps
import FunUniverse.Cost as Cost
module TimeCost = FunOps Cost.timeOps
{-
putBit : 𝟚 → IO 𝟙
putBit 1₂ = putStr "1"
putBit 0₂ = putStr "0"
putBits : ∀ {n} → Vec 𝟚 n → IO 𝟙
putBits [] = return _
putBits (x ∷ bs) = ♯ putBit x >> ♯ putBits bs
-}
arg1   = ℕ▹`Bits 8 0x0b _
arg2   = ℕ▹`Bits 8 0x1f _
result = adder (arg1 , arg2)
adder-cost : ℕ → ℕ
adder-cost n = FunAdder.adder Cost.timeOps {n}
{-
mainIO : IO 𝟙
mainIO = ♯ putBits arg1 >>
      ♯ (♯ putStr " + " >>
      ♯ (♯ putBits arg2 >>
      ♯ (♯ putStr " = " >>
      ♯ (♯ putBits result >>
      ♯ (♯ putStr " cost:" >>
         ♯ putStr (show (adder-cost 8)))))))
main : IO.Primitive.IO 𝟙
main = IO.run mainIO
-}

{- Separating Random Oracle Proofs from
   Complexity Theoretic Proofs:
   The Non-committing Encryption Case

NCE: Non-committing Encryption
-}

open import Function
open import Type using (★)
open import Data.Product
open import Data.One
open import Data.Two
open import Control.Beh

module Game.NCE
  (MId PId Msg Len : ★)
  (length : Msg → Len)
  (A : PId) -- adversary PId
  (F : PId) -- functionality PId (Fnce)
  where

S : 𝟚 → ★
S = [0: MId × PId × Msg
     1: MId × PId × PId × Len ]

Ideal-Fnce' : Beh PId 𝟙 𝟙 𝟙 (S 0₂) (Σ 𝟚 S) 𝟙
Ideal-Fnce' = input (λ { i (mid , j , msg) →
                 output j (0₂ , mid , i , msg)
                  (output A (1₂ , mid , i , j , length msg)
                   end) })

Ideal-Fnce : Beh PId 𝟙 𝟙 𝟙 (Σ 𝟚 S) (Σ 𝟚 S) 𝟙
Ideal-Fnce = input (λ i m →
               case m of λ
               { (0₂ , mid , j , msg) →
                 output j (0₂ , mid , i , msg)
                  (output A (1₂ , mid , i , j , length msg)
                   end)
               ; (1₂ , _) → end
               })

PlainText = Σ 𝟚 S
module Real
  (SecKey PubKey Rₑ CipherText : ★)
  (pk  : PId → PubKey)
  (Enc : PubKey → Rₑ → PlainText → CipherText)
  (Dec : SecKey → CipherText → PlainText)
  where

    Real-Fnce : Beh PId SecKey 𝟙 Rₑ CipherText CipherText 𝟙
    Real-Fnce =
     input λ i c →
      ask λ sk →
       case Dec sk c of λ
       { (0₂ , (mid , j , m)) →
        rand λ rₑ →
         output j (Enc (pk j) rₑ (0₂ , mid , i , m))
          (rand λ rₑ →
            output A
              (Enc (pk A) rₑ (1₂ , mid , i , j , length m))
            end)
       ; (1₂ , _) → end
       }

module Sim where
  open Sim[E=𝟙,R=1] {PId} {𝟙} {Σ 𝟚 S} {Σ 𝟚 S} {𝟙}
    public

  end-end : end ≈ end
  end-end = return-return _

module DummyCrypto where
  open Real 𝟙 𝟙 𝟙 (Σ 𝟚 S) (const _) (λ _ _ m → m) (λ _ m → m)
  open Sim

  p : Ideal-Fnce ≈ Real-Fnce
  p = input-input (λ i m → nop-ask (helper i m)) where
    helper : (i : PId) (m : Σ 𝟚 S) → _ ≈ _
    helper i (0₂ , m) =
      nop-rand
        (output-output
           (nop-rand
              (output-output end-end)))
    helper i (1₂ , m) =
      end-end
-- -}

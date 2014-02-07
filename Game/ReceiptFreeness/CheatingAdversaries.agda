{-# OPTIONS --copatterns #-}


  {- Not all adversaries of the Adversary type are valid.
  
     First, we do not forbid the challenge in the 2nd step of the Oracle.
     Second, there is no check preventing ballots to be resubmitted.
     Last but not least, no complexity analysis is done.
  -}

open import Function
open import Type
open import Data.Fin.NP using (Fin)
open import Data.List as L
open import Data.Nat.NP using (ℕ) renaming (_==_ to _==ℕ_)
open import Data.Product
open import Data.Two
open import Game.Challenge
open import Control.Strategy
open import Data.List.Any using (here; there)
open Data.List.Any.Membership-≡ using (_∈_ ; _∉_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP

module Game.ReceiptFreeness.CheatingAdversaries
  (PubKey    : ★)
  (SecKey    : ★)
  -- Message = 𝟚
  (CipherText : ★)

  (SerialNumber : ★)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ Rₖ Rₐ : ★)
  (#q : ℕ) (max#q : Fin #q)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : let Message = 𝟚 in
            PubKey → Message → Rₑ → CipherText)
  (Dec    : let Message = 𝟚 in
            SecKey → CipherText → Message)
  where

open import Game.ReceiptFreeness PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen Enc Dec


module _ 
  (Check : BB → Receipt → 𝟚)
  (CheckMem : ∀ bb r → ✓ (Check bb r) → proj₁ (proj₂ r) ∉ L.map (proj₁ ∘ proj₂) bb)
  where

  open Experiment Check
  
  module Cheating1 (sn : SerialNumber ²) where
      cheatingA : Adversary
      cheatingA rₐ pk = done chal where
        chal : ChalAdversary _ _ _
        get-chal chal = sn
        put-resp chal m = ask (RCO (m 1₂)) (λ co → done (co == (marked-on-second-cell? (markedReceipt? (m 1₂)))))
      module _
       (DecEnc : ∀ rₖ rₑ m → let (pk , sk) = KeyGen rₖ in
                             Dec sk (Enc pk m rₑ) ≡ m) where
  
          cheatingA-wins : ∀ r → game cheatingA r ≡ 1₂
          cheatingA-wins (rₖ , _ , b₂ , rₑ , _)
            rewrite DecEnc rₖ (rₑ 1₂) (not b₂) with b₂
          ... | 0₂ = refl
          ... | 1₂ = refl
  
      module _ {rₐ pk sn ci} where
        notValid : ¬ (Valid-Adversary cheatingA)
        notValid va = proj₂ (proj₁ (proj₂ (proj₂ (va rₐ pk)) (λ _ → not-marked , sn , ci))) refl
      
          
  module TriesToCheatByReVotingButItsRejected (sn : SerialNumber ²) where
      cheatingA : Adversary
      cheatingA rₐ pk = done chal where
        chal : ChalAdversary _ (Receipt ²) (Strategy Q Resp 𝟚)
        get-chal chal = sn
        put-resp chal m = ask (Vote (m 1₂))
          (λ { accept → ask RTally (λ { (x , y) → done (x ==ℕ 2) })
             ; reject → done 1₂ })
  
      module _ rₖ rₐ b rₑ rgbs
       (DecEnc : ∀ b m → let (pk , sk) = KeyGen rₖ in
                       Dec sk (Enc pk m (rₑ b)) ≡ m) where
  
          r : R
          r = rₖ , rₐ , b , rₑ , rgbs
  
          pk = proj₁ (KeyGen rₖ)
          sk = proj₂ (KeyGen rₖ)
          
          module E = EXP b cheatingA pk sk rₐ rgbs rₑ
          ballot = marked 0₂ ,′ sn 1₂ , Enc pk (not b) (rₑ 1₂)
          
          cheatingA-busted : game cheatingA r ≡ b
          cheatingA-busted with Check E.BBrfc ballot
                            | CheckMem E.BBrfc ballot
          cheatingA-busted | 1₂ | pr with pr _ (there (here refl))
          ... | ()
          cheatingA-busted | 0₂ | _ with b
          ... | 0₂ = refl
          ... | 1₂ = refl

      valid : Valid-Adversary cheatingA
      valid rₐ pk = (λ ()) , (λ ()) , λ _ → λ { accept r → _ ; reject → _ }
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

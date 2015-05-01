{-# OPTIONS --without-K --copatterns #-}

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
open import Data.Product.NP
open import Data.Two
open import Data.Maybe
open import Game.Challenge
open import Control.Strategy
open import Data.List.Any using (here; there)
open Data.List.Any.Membership-≡ using (_∈_ ; _∉_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP

open import Crypto.Schemes

module Game.ReceiptFreeness.CheatingAdversaries
  (pke : Pubkey-encryption)
  (open Pubkey-encryption pke)
  (SerialNumber : Type)
  (Rₐ : Type)
  (𝟚→Message : 𝟚 → Message)
  (Message→𝟚 : Maybe Message → 𝟚)
  (#q : ℕ) (max#q : Fin #q)
  where

open import Game.ReceiptFreeness pke SerialNumber Rₑ 𝟚→Message Message→𝟚 #q max#q

{-
module _ 
  (Check : BB → Receipt → 𝟚)
  (CheckMem : ∀ bb r → ✓ (Check bb r) → fst (snd r) ∉ L.map (fst ∘ snd) bb)
  where

  open Experiment Check
  
  module Cheating1 (sn : SerialNumber ²) where
      cheatingA : Adversary
      cheatingA rₐ pk = done chal where
        chal : ChalAdversary _ _ _
        get-chal chal = sn
        put-resp chal m = ask (RCO (m 1₂)) (λ co → done (co == (marked-on-second-cell? (markedReceipt? (m 1₂)))))
      module _
       (DecEnc : ∀ rₖ rₑ m → let (pk , sk) = key-gen rₖ in
                             dec sk (enc pk m rₑ) ≡ m) where
  
          cheatingA-wins : ∀ r → game cheatingA r ≡ 1₂
          cheatingA-wins (rₖ , _ , b₂ , rₑ , _)
            rewrite DecEnc rₖ (rₑ 1₂) (not b₂) with b₂
          ... | 0₂ = refl
          ... | 1₂ = refl
  
      module _ {rₐ pk sn ci} where
        notValid : ¬ (Valid-Adversary cheatingA)
        notValid va = snd (fst (snd (snd (va rₐ pk)) (λ _ → not-marked , sn , ci))) refl
      
          
  module TriesToCheatByReVotingButItsRejected (sn : SerialNumber ²) where
      cheatingA : Adversary
      cheatingA rₐ pk = done chal where
        chal : ChalAdversary _ (Receipt ²) (Strategy Q Resp 𝟚)
        get-chal chal = sn
        put-resp chal m = ask (Vote (m 1₂))
          (λ { accept → ask RTally (λ { (x , y) → done (x ==ℕ 2) })
             ; reject → done 1₂ })
  
      module _ rₖ rₐ b rₑ rgbs
       (DecEnc : ∀ b m → let (pk , sk) = key-gen rₖ in
                       dec sk (enc pk m (rₑ b)) ≡ m) where
  
          r : R
          r = rₖ , rₐ , b , rₑ , rgbs
  
          pk = fst (key-gen rₖ)
          sk = snd (key-gen rₖ)
          
          module E = EXP b cheatingA pk sk rₐ rgbs rₑ
          ballot = marked 0₂ ,′ sn 1₂ , enc pk (not b) (rₑ 1₂)
          
          cheatingA-busted : game cheatingA r ≡ b
          cheatingA-busted with Check E.BBrfc ballot
                            | CheckMem E.BBrfc ballot
          cheatingA-busted | 1₂ | pr with pr _ (there (here refl))
          ... | ()
          cheatingA-busted | 0₂ | _ = helper b
              where helper : ∀ b → not b xor 1₂ ≡ b
                    helper 1₂ = refl
                    helper 0₂ = refl

      valid : Valid-Adversary cheatingA
      valid rₐ pk = (λ ()) , (λ ()) , λ _ → λ { accept r → _ ; reject → _ }
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

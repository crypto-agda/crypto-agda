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
import Data.List.Any as LA

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP

open module MM {X : ★} = LA.Membership (setoid X)

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


open import Game.ReceiptFreeness.Definitions PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen Enc Dec

module _ 
  (Check : BB → Receipt → 𝟚)
  (CheckMem : ∀ bb r → ✓ (Check bb r) → proj₁ (proj₂ r) ∉ L.map (proj₁ ∘ proj₂) bb)
  where

  open import Game.ReceiptFreeness.Experiment PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen Enc Dec Check CheckMem
  open import Game.ReceiptFreeness.Valid PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen Enc Dec
  
  module Cheating1 (sn : SerialNumber ²) where
      open SimpleScheme 
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
      
          
  module Cheating2 (sn : SerialNumber ²) where
      open SimpleScheme
      cheatingA : Adversary
      cheatingA rₐ pk = done chal where
        chal : ChalAdversary _ (Receipt ²) (Strategy Q Resp 𝟚)
        get-chal chal = sn
        put-resp chal m = ask (Vote (m 1₂))
          (λ { accept → ask RTally (λ { (x , y) → done (x ==ℕ 2) })
             ; reject → done 1₂ })
  
      module _
       (rₖ : _)(rₐ : _)(b : _)(rₑ : _)(rgbs : _)
       (DecEnc : ∀ b m → let (pk , sk) = KeyGen rₖ in
                       Dec sk (Enc pk m (rₑ b)) ≡ m) where
  
          r : R
          r = rₖ , rₐ , b , rₑ , rgbs
  
          pk = proj₁ (KeyGen rₖ)
          sk = proj₂ (KeyGen rₖ)
          
          module E = EXP cheatingA pk sk rₐ rgbs (ct-resp b pk rₑ) (const (marked 0₂))
          ballot = marked 0₂ ,′ sn 1₂ , Enc pk (not b) (rₑ 1₂)
          
          cheatingA-wins : game cheatingA r ≡ b
          cheatingA-wins with Check E.BBrfc ballot
                            | CheckMem E.BBrfc ballot
          cheatingA-wins | 1₂ | pr with pr _ (LA.there (LA.here refl))
          ... | ()
          cheatingA-wins | 0₂ | _ with b
          ... | 0₂ = refl
          ... | 1₂ = refl
      module _  where
        valid : Valid-Adversary cheatingA
        valid rₐ pk = (λ ()) , (λ ()) , (λ { r₁ accept r → _ ; r₁ reject → _ })

          {-
             rewrite CheckEnc (proj₁ (KeyGen rₖ)) (co 1₂) (rₑ 1₂)
                   | DecEnc rₖ (rₑ 0₂) (co 0₂)
                   | DecEnc rₖ (rₑ 1₂) (co 1₂) with co 0₂ | co 1₂
          ... | 0₂ | 0₂ = refl
          ... | 0₂ | 1₂ = refl
          ... | 1₂ | 0₂ = refl
          ... | 1₂ | 1₂ = refl
          cheatingA-wins (rₖ , _ , 1₂ , co , rₑ , _)
             rewrite CheckEnc (proj₁ (KeyGen rₖ)) (co 0₂) (rₑ 0₂)
                   | DecEnc rₖ (rₑ 0₂) (co 0₂)
                   | DecEnc rₖ (rₑ 1₂) (co 1₂) with co 0₂ | co 1₂
          ... | 0₂ | 0₂ = refl
          ... | 0₂ | 1₂ = refl
          ... | 1₂ | 0₂ = refl
          ... | 1₂ | 1₂ = refl
          -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

open import Type
open import Data.List
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
{-
open import Data.Zero
open import Data.One
open import Data.Nat
-}
open import Data.Two
open import Control.Strategy

module Helios
  (VoterId : ★)
  (PublicKey : ★)
  (SecretKey : ★)
  (Vote   : ★)
  (Ballot : ★)
  (Decryption-share : ★)
  (PublicInfo : ★)
  where

Ballots = List (VoterId × Ballot)
Decryption-shares = List Decryption-share

record BB : ★ where
  constructor <_,,_,,_>
  field
    Y-pk              : PublicKey
    ballots           : Ballots
    decryption-shares : Decryption-shares
open BB public

module Nested
  (R-setup : ★)
  (setup : R-setup → PublicKey × {-List-} SecretKey)
  (R-vote : ★)

  (vote : PublicKey → R-vote → VoterId → Vote → Ballot)
  (validate : BB → VoterId × Ballot → 𝟚)

  (Tally : ★) -- could be a valid tally or a special symbol ⊥
  (dec-shares : PublicKey → Ballots → {-List-} SecretKey → Decryption-shares)
  (result : BB → Tally)

  (R-adversary : ★)
  where

  tally : BB → {-List-} SecretKey → BB
  tally < Y ,, bs ,, ds > sks = < Y ,, bs ,, dec-shares Y bs sks >

  data Q : ★ where
    ask-vote   : (v_ : Vote ²) → Q
    ask-ballot : (b  : Ballot) → Q

  VotingPhase = List (BB → VoterId × Q)

  add-ballot : VoterId → Ballot → BB → BB
  add-ballot vid b bb = record bb { ballots = (vid , b) ∷ ballots bb }

  module Run (β : 𝟚)
             (pk : PublicKey)
             (r-votes : VoterId → R-vote ²)
           where

    run-query : VoterId → Q → BB ² → BB ²
    run-query vid (ask-vote v_)  bb_ i = case validate (bb_ i) (vid , b)
                                          0: bb_ i
                                          1: add-ballot vid b (bb_ i)
      where
        b : Ballot
        b = vote pk (r-votes vid i) vid (v i)

    run-query vid (ask-ballot b) bb_ i =
        case validate (bb_ β) (vid , b)
          0: bb_ i
          1: case validate (bb_ (not β)) (vid , b)
               0: case i
                    0: add-ballot vid b (bb_ 0₂)
                    1: bb_ 1₂
               1: add-ballot vid b (bb_ i)

    run-voting-phase : VotingPhase → BB ² → BB ²
    run-voting-phase []       bb_ = bb_
    run-voting-phase (q ∷ qs) bb_ = run-voting-phase qs (uncurry run-query (q (bb_ β)) bb_)

  Adversary = R-adversary →
              PublicKey →
              VotingPhase ×
              (BB →
              𝟚)

  module Game (β : 𝟚)
              (r-setup : R-setup)
              (r-votes : VoterId → R-vote ²)
              (r-adversary : R-adversary)
              (A : Adversary)
              where
    pksk = setup r-setup
    pk = fst pksk
    sk = snd pksk

    BB-setup : BB
    BB-setup = < pk ,, [] ,, [] >

    BB²-setup : BB ²
    BB²-setup _ = BB-setup

    A-setup = A r-adversary pk

    A-voting-phase : VotingPhase
    A-voting-phase = fst A-setup

    open Run β pk r-votes

    exp : 𝟚
    exp = snd A-setup (run-voting-phase A-voting-phase BB²-setup β)

    game = exp == β
-- -}
-- -}
-- -}
-- -}
-- -}

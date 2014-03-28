open import Type
open import Function
open import Data.List
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
{-
open import Data.Zero
open import Data.One
-}
open import Data.Two
open import Data.Nat.NP hiding (_==_; _<_)
open import Control.Strategy

module Helios
  (VoterId : ★)
  (PublicKey : ★)
  (SecretKey : ★)
  (NIZKSecretKey : PublicKey → ★)
  (Vote   : ★)
  (Ballot : ★)
  (Decryption-share : ★)
  (PublicInfo : ★)
  (R-setup : ★)
  (R-vote : ★)
  (vote : PublicKey → R-vote → VoterId → Vote → Ballot)
  (let Ballots = List (VoterId × Ballot)
       Decryption-shares = List Decryption-share
  )
  (validate-ballots : PublicKey → Ballots → 𝟚)
  (Tally : ★) -- could be a valid tally or a special symbol ⊥
  (fake-decrytion-share : Tally → Ballots → Decryption-share)
  (R-adversary : ★)
  where

record KeyPair : ★ where
  constructor mk
  field
    pk : PublicKey
    sk : SecretKey
    zk : NIZKSecretKey pk


record BB : ★ where
  constructor <_,,_,,_,,_>
  field
    Y-pk              : PublicKey
    π-pk              : NIZKSecretKey Y-pk
    ballots           : Ballots
    decryption-shares : Decryption-shares
open BB public

Make-decryption-shares = KeyPair → Ballots → Decryption-shares
Simulate-decryption-shares = (bs₀ : Ballots) → Make-decryption-shares

validate : PublicKey → Ballots → VoterId × Ballot → 𝟚
validate pk bs vb = validate-ballots pk (vb ∷ bs)

data Q : ★ where
  ask-vote   : (v_ : Vote ²) → Q
  ask-ballot : (b  : Ballot) → Q

VotingPhase = List (Ballots → VoterId × Q)

module Tallying
  (decryption-shares : Make-decryption-shares)
  (result : BB → Tally)
  where

  tally-bb : KeyPair → Ballots → BB
  tally-bb (mk Y sk zk) bs = < Y ,, zk ,, bs ,, decryption-shares (mk Y sk zk) bs >

  tally : KeyPair → Ballots → Tally
  tally kp bs = result (tally-bb kp bs)

module Run-common
           (pk : PublicKey)
           (r-votes : VoterId → R-vote ²) where
    run-vote-query¹ : R-vote → VoterId → Vote → Ballots → Ballots
    run-vote-query¹ r-vote vid v bs = case validate pk bs (vid , b)
                                        0: bs
                                        1: ((vid , b) ∷ bs)
      where
        b : Ballot
        b = vote pk r-vote vid v

    run-vote-query : (hack-run-vote-query : 𝟚 → 𝟚) → VoterId → Vote ² → Ballots ² → Ballots ²
    run-vote-query hack-run-vote-query vid v_ bs_ i = run-vote-query¹ (r-votes vid i) vid (v_ (hack-run-vote-query i)) (bs_ i)

    run-ballot-query : (β : 𝟚) → VoterId → Ballot → Ballots ² → Ballots ²
    run-ballot-query β vid b bs_ i =
        case validate pk (bs_ β) (vid , b)
          0: bs_ i
          1: case validate pk (bs_ (not β)) (vid , b)
               0: case i
                    0: ((vid , b) ∷ bs_ 0₂)
                    1: bs_ 1₂
               1: ((vid , b) ∷ bs_ i)

Hack-run-vote-query = ℕ → 𝟚 → 𝟚

module Run (β : 𝟚)
           (hack-run-vote-query : Hack-run-vote-query)
           (pk : PublicKey)
           (r-votes : VoterId → R-vote ²) where
    open Run-common pk r-votes

    run-query : (hack-run-vote-query : 𝟚 → 𝟚) → VoterId → Q → Ballots ² → Ballots ²
    run-query hack-run-vote-query vid (ask-vote v_)  = run-vote-query hack-run-vote-query vid v_
    run-query hack-run-vote-query vid (ask-ballot b) = run-ballot-query β vid b

    run-voting-phase : VotingPhase → Ballots ² → Ballots ²
    run-voting-phase []       bs_ = bs_
    run-voting-phase (q ∷ qs) bs_ = run-voting-phase qs (uncurry (run-query (hack-run-vote-query (length qs))) (q (bs_ β)) bs_)

module _ where
  Adversary = R-adversary →
              PublicKey →
              VotingPhase ×
              (BB →
              𝟚)

  module CommonChallenger
              (setup : R-setup → KeyPair)
              (r-setup : R-setup)
              (r-adversary : R-adversary)
              (A : Adversary)
              where
    kp = setup r-setup
    open KeyPair kp public

    A-setup = A r-adversary pk

    A-voting-phase : VotingPhase
    A-voting-phase = fst A-setup

  -- The real challenger (has access to β)
  module Game (setup : R-setup → KeyPair)
              (decryption-shares : Make-decryption-shares)
              (hack-run-vote-query : Hack-run-vote-query)

              (r-setup : R-setup)
              (r-adversary : R-adversary)
              (A : Adversary)
              (r-votes : VoterId → R-vote ²)
              (simulate-decryption-shares : Simulate-decryption-shares)
              (β : 𝟚)
              where
    open CommonChallenger setup r-setup r-adversary A public

    open Run β hack-run-vote-query pk r-votes

    bs_ : Ballots ²
    bs_ = run-voting-phase A-voting-phase (const [])

    decryption-shares-β =
      (case β
         0: decryption-shares
         1: simulate-decryption-shares (bs_ 0₂))
      kp (bs_ β)

    bb : BB
    bb = record { Y-pk = pk ; π-pk = zk ; ballots = bs_ β ; decryption-shares = decryption-shares-β }

    exp : 𝟚
    exp = snd A-setup bb

    game = exp == β

  module Unused-simulate-decryption-shares
              (decryption-shares : Make-decryption-shares)
              (result : BB → Tally)
              (kp  : KeyPair)
              (bs_ : Ballots ²)
           where
    open KeyPair kp
    open Tallying decryption-shares result
    simulated-decryption-shares : Decryption-shares
    simulated-decryption-shares = fake-decrytion-share (tally kp (bs_ 0₂)) (bs_ 1₂) ∷ []

    {-
  module Simulated-Challenger
              (r-setup : R-setup)
              (r-votes : VoterId → R-vote ²)
              (r-adversary : R-adversary)
              (A : Adversary)
            where
    open CommonChallenger r-setup r-adversary A public
-}
  module Proof (setup : R-setup → KeyPair)
               (result : BB → Tally)
               (decryption-shares  decryption-sharesₐ : Make-decryption-shares)
               (r-setup : R-setup)
               (r-adversary : R-adversary)
               (A : Adversary)
               (r-votes : VoterId → R-vote ²)
               (simulate-decryption-shares : Simulate-decryption-shares)
               (simulate-zksecret : (pk : PublicKey) → NIZKSecretKey pk)
               where
     hack-no-queries : Hack-run-vote-query
     hack-no-queries = const id
     module EXP = Game setup decryption-shares hack-no-queries r-setup r-adversary A r-votes simulate-decryption-shares
     G₀ = EXP.exp 0₂
     G₁ = EXP.exp 1₂

     setupₐ : R-setup → KeyPair
     setupₐ r-setup = record (setup r-setup) { zk = simulate-zksecret _ }

     module EXPₐ = Game setupₐ decryption-sharesₐ hack-no-queries r-setup r-adversary A r-votes simulate-decryption-shares 0₂

     Gₐ = EXPₐ.exp

     simulate-decryption-shares-B : Make-decryption-shares
     simulate-decryption-shares-B kp bs = fake-decrytion-share t bs ∷ []
       where
         open Tallying decryption-sharesₐ result
         t  = tally kp bs

     module EXP-B = Game setupₐ simulate-decryption-shares-B hack-no-queries r-setup r-adversary A r-votes (λ _ _ _ → {- unused -} []) 0₂

     G-B = EXP-B.exp

     hack-all-queries : Hack-run-vote-query
     hack-all-queries = const not

     Seq : ★ → ★
     Seq A = ℕ → A

     _<_ : ℕ → ℕ → 𝟚
     x < y = suc x <= y

     replicateSeq : {A : ★} → ℕ → A → A → Seq A
     replicateSeq n x y i = case (i < n) 0: x 1: y

     hack-queries-up-to : ℕ → Hack-run-vote-query
     hack-queries-up-to n i = replicateSeq (n id not i

     module EXP-C-up-to (n : ℕ) = Game setupₐ simulate-decryption-shares-B (hack-queries-up-to n) r-setup r-adversary A r-votes (λ _ _ _ → {- unused -} []) 0₂

     module EXP-C = Game setupₐ simulate-decryption-shares-B hack-all-queries r-setup r-adversary A r-votes (λ _ _ _ → {- unused -} []) 0₂

     G-C = EXP-C.exp

     {- EXP-C-up-to zero -}

     -- G₀∼Gₐ
-- -}
-- -}
-- -}
-- -}
-- -}

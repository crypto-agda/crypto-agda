open import Type
open import Function
open import Data.List
open import Data.Vec using (Vec; []; _∷_)
open import Data.Fin using (Fin; zero; suc) renaming (toℕ to Fin▹ℕ)
open import Data.Product.NP renaming (proj₁ to fst; proj₂ to snd) hiding (zip; map)
{-
open import Data.Zero
open import Data.One
-}
open import Data.Two
open import Data.Nat.NP hiding (_==_; _<_)
--open import Control.Strategy

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
  {-
  (let Ballots = List (VoterId × Ballot)
       Decryption-shares = List Decryption-share
  )
  -}
  (validate-ballots :
     let Ballots = List (VoterId × Ballot)
         Decryption-shares = List Decryption-share in
     PublicKey → Ballots → 𝟚)
  (Tally : ★) -- could be a valid tally or a special symbol ⊥
  (fake-decrytion-share :
     let Ballots = List (VoterId × Ballot)
         Decryption-shares = List Decryption-share in
     Tally → Ballots → Decryption-share)
  (R-adversary : ★)
  where

Ballots = List (VoterId × Ballot)
Decryption-shares = List Decryption-share

module _ {A : ★} where
  map-nᵗʰ : ℕ → (A → A) → List A → List A
  map-nᵗʰ n       f []       = []
  map-nᵗʰ zero    f (x ∷ xs) = f x ∷ xs
  map-nᵗʰ (suc n) f (x ∷ xs) = x ∷ map-nᵗʰ n f xs

_<_ : ℕ → ℕ → 𝟚
x < y = suc x <= y

module _ {k : ℕ} {- sequences -} where
     Seq : ★ → ★
     Seq A = Fin k → A

     {-
     replicateSeq : {A : ★} → Fin k → A → A → Seq A
     replicateSeq n x y i = case {!(i < n)!} 0: x 1: y
     -}

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

map-vote²-Q : (Vote ² → Vote ²) → Q → Q
map-vote²-Q f (ask-vote v_) = ask-vote (f v_)
map-vote²-Q f (ask-ballot b) = ask-ballot b

VotingPhase₀ : ★
VotingPhase₀ = Ballots → VoterId × Q

VotingPhase : ★
VotingPhase = List VotingPhase₀

module Tallying
  (decryption-shares : Make-decryption-shares)
  (result : BB → Tally)
  where

  tally-bb : KeyPair → Ballots → BB
  tally-bb (mk Y sk zk) bs = < Y ,, zk ,, bs ,, decryption-shares (mk Y sk zk) bs >

  tally : KeyPair → Ballots → Tally
  tally kp bs = result (tally-bb kp bs)

module Run-common (pk : PublicKey) where
    run-vote-query¹ : R-vote → VoterId → Vote → Ballots → Ballots
    run-vote-query¹ r-vote vid v bs = case validate pk bs (vid , b)
                                        0: bs
                                        1: ((vid , b) ∷ bs)
      where
        b : Ballot
        b = vote pk r-vote vid v

    run-vote-query : R-vote ² → VoterId → Vote ² → Ballots ² → Ballots ²
    run-vote-query r-vote vid v_ bs_ i = run-vote-query¹ (r-vote i) vid (v_ i) (bs_ i)

    run-ballot-query : (β : 𝟚) → VoterId → Ballot → Ballots ² → Ballots ²
    run-ballot-query β vid b bs_ i =
        case validate pk (bs_ β) (vid , b)
          0: bs_ i
          1: case validate pk (bs_ (not β)) (vid , b)
               0: case i
                    0: ((vid , b) ∷ bs_ 0₂)
                    1: bs_ 1₂
               1: ((vid , b) ∷ bs_ i)

module Run (β : 𝟚) (pk : PublicKey) where
    open Run-common pk

    run-query : R-vote ² → VoterId → Q → Ballots ² → Ballots ²
    run-query r-vote vid (ask-vote v_)  = run-vote-query r-vote vid v_
    run-query r-vote vid (ask-ballot b) = run-ballot-query β vid b

    run-voting-phase : List (VotingPhase₀ × R-vote ²) → Ballots ² → Ballots ²
    run-voting-phase []                  bs_ = bs_
    run-voting-phase ((q , r-vote) ∷ qs) bs_ =
       run-voting-phase qs (uncurry (run-query r-vote) (q (bs_ β)) bs_)

Hack-run-vote-query : ℕ → ★
Hack-run-vote-query #q = Fin #q → 𝟚 → 𝟚

module _ {-(max-q-1 : ℕ)-} where
  -- max-q = ℕ.suc max-q-1
  Adversary = R-adversary →
              PublicKey →
              -- Σ _ λ (#q : Fin max-q) →
              VotingPhase × -- (Fin▹ℕ #q) ×
              (BB →
              𝟚)

  map-vote²-in-voting-phase : (Vote ² → Vote ²) → VotingPhase₀ → VotingPhase₀
  map-vote²-in-voting-phase f = _∘_ (second (map-vote²-Q f))

  map-Advesary : (VotingPhase → VotingPhase) → Adversary → Adversary
  map-Advesary f A rₐ pk = first f (A rₐ pk)

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

              (r-setup : R-setup)
              (r-adversary : R-adversary)
              (A : Adversary)
              -- (hack-run-vote-queries : VotingPhase → VotingPhase)
              -- (hack-run-vote-query : (x : Fin max-q) → Hack-run-vote-query (Fin▹ℕ x))
              (r-votes : List (R-vote ²))
              (simulate-decryption-shares : Simulate-decryption-shares)
              (β : 𝟚)
              where

    open CommonChallenger setup r-setup r-adversary A public

    open Run β pk

    -- zip : ∀ {n m} {o : Fin n} (xs : Vec A (Fin▹ℕ o)) (ys : Vec A

    voting-phase : List (VotingPhase₀ × R-vote ²)
    voting-phase = zip A-voting-phase r-votes

    bs_ : Ballots ²
    bs_ = run-voting-phase voting-phase (const [])

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
               -- (r-votes : (x : Fin max-q) (y : Fin (Fin▹ℕ x)) → R-vote ²)
               (r-votes : List (R-vote ²))
               (simulate-decryption-shares : Simulate-decryption-shares)
               (simulate-zksecret : (pk : PublicKey) → NIZKSecretKey pk)
               where
     hack-voting-phase₀ = map-vote²-in-voting-phase (λ v i → v (not i))

     hack-all-queries : Adversary → Adversary
     hack-all-queries = map-Advesary (map hack-voting-phase₀)

     hack-query : ℕ → Adversary → Adversary
     hack-query n = map-Advesary (map-nᵗʰ n hack-voting-phase₀)

     hack-upto : ℕ → Adversary → Adversary
     hack-upto zero    = id
     hack-upto (suc n) = hack-upto n ∘ hack-query n

     module EXP = Game setup decryption-shares r-setup r-adversary A r-votes simulate-decryption-shares
     G₀ = EXP.exp 0₂
     G₁ = EXP.exp 1₂

     setupₐ : R-setup → KeyPair
     setupₐ r-setup = record (setup r-setup) { zk = simulate-zksecret _ }

     {-
     from G₀
       change setup             to setupₐ
       change decryption-shares to decryption-sharesₐ

       because β ≡ 0₂ simulate-decryption-shares is not used
     -}
     module EXPₐ = Game setupₐ decryption-sharesₐ r-setup r-adversary A r-votes (λ _ _ _ → {- unused -} []) 0₂

     Gₐ = EXPₐ.exp

     -- TODO: G₀ ≈ Gₐ

     simulate-decryption-shares-B : Make-decryption-shares
     simulate-decryption-shares-B kp bs = fake-decrytion-share t bs ∷ []
       where
         open Tallying decryption-sharesₐ result
         t  = tally kp bs

     {-
     from Gₐ
       change decryption-sharesₐ to simulate-decryption-shares-B
     -}
     module EXP-B = Game setupₐ simulate-decryption-shares-B r-setup r-adversary A r-votes (λ _ _ _ → {- unused -} []) 0₂
     G-B = EXP-B.exp

     {-
     G-C-last 0 is EXP-B
     -}
     module EXP-C-nᵗʰ (n : ℕ) = Game setupₐ simulate-decryption-shares-B r-setup r-adversary (hack-query n A) r-votes (λ _ _ _ → {- unused -} []) 0₂
     module EXP-C-upto (n : ℕ) = Game setupₐ simulate-decryption-shares-B r-setup r-adversary (hack-upto n A) r-votes (λ _ _ _ → {- unused -} []) 0₂

     {-
     like G-B but all vote queries are "hacked", namely moved from left(0₂) to right(1₂)
     -}
     module EXP-C = Game setupₐ simulate-decryption-shares-B r-setup r-adversary (hack-all-queries A) r-votes (λ _ _ _ → {- unused -} []) 0₂
     G-C = EXP-C.exp

     {- (revert Gₐ→G-B)
     from G-C
       change simulate-decryption-shares-B to decryption-sharesₐ
     -}
     module EXP-D = Game setupₐ decryption-sharesₐ r-setup r-adversary (hack-all-queries A) r-votes (λ _ _ _ → {- unused -} []) 0₂
     G-D = EXP-D.exp

     {- (revert G₀→Gₐ)
     from G-D
       change setupₐ             to setup
       change decryption-sharesₐ to decryption-shares
     -}
     module EXP-E = Game setup decryption-shares r-setup r-adversary (hack-all-queries A) r-votes (λ _ _ _ → {- unused -} []) 0₂
     G-E = EXP-E.exp

     -- G-E ≈ G₁

-- -}
-- -}
-- -}
-- -}
-- -}

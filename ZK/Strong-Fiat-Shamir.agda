-- http://www.uclouvain.be/crypto/services/download/publications.pdf.87e67d05ee05000b.6d61696e2e706466.pdf
open import Type using (Type; Type₁)
open import Function.NP
open import Data.Maybe
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Nat
open import Data.Sum using (_⊎_)
open import Data.List.NP renaming (map to mapᴸ)
open import Data.List.Any using (module Membership-≡ ; Any ; here ; there)
open Membership-≡ using (_∈_)
open import Data.Product.NP
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.NP
open import Control.Strategy using (Strategy; module TranscriptRun; module TranscriptConstRun; module RepeatIndex ; done; ask ; run)
  renaming (map to mapS)

module ZK.Strong-Fiat-Shamir
  {W Λ : Type}{L : W → Λ → Type}
  (any-W : W)
  {RS : Type}
  (L? : ∀ w Y → Dec (L w Y))
  (Λ? : Decidable (_≡_ {A = Λ}))
  (Eps  : Type)
  (ε[_] : Eps → Type)
  (ε0 : Eps)
  (ε[0] : ε[ ε0 ] ≡ 𝟘)
  where

valid-witness? : W → Λ → 𝟚
valid-witness? w Y = ⌊ L? w Y ⌋

valid-witnesses? : List W → List Λ → 𝟚
valid-witnesses? [] [] = 1₂
valid-witnesses? (w ∷ ws) (prf ∷ prfs) = valid-witness? w prf ∧ valid-witnesses? ws prfs
valid-witnesses? _ _ = 0₂

module _ {R : Type} where
    _≋_ : (f g : R → 𝟚) → Type₁
    f ≋ g = (Σ R (✓ ∘ f)) ≡ (Σ R (✓ ∘ g))

    _≈_ : (f g : R → 𝟚) → Type₁
    f ≈ g = ∃₂ λ ε₀ ε₁ →
            (Σ R (✓ ∘ f) ⊎ ε[ ε₀ ]) ≡ (Σ R (✓ ∘ g) ⊎ ε[ ε₁ ])

    ≋→≈ : ∀ {f g} → f ≋ g → f ≈ g
    ≋→≈ f≋g = ε0 , ε0 , ap (flip _⊎_ ε[ ε0 ]) f≋g

{-
Random-Oracle-List : Type
Random-Oracle-List = List (Q × Resp)
-}

record Proof-System (RP : Type)(Prf : Λ → Type) : Type where
  field
    Prove  : RP → (w : W)(Y : Λ) → Prf Y
    Verify : (Y : Λ)(π : Prf Y) → 𝟚

  Complete : Type
  Complete = ∀ rp {w Y} → L w Y → Verify Y (Prove rp w Y) ≡ 1₂

  -- Not in the paper but...
  Sound : Type
  Sound = ∀ rp {w Y} → Verify Y (Prove rp w Y) ≡ 1₂ → L w Y

module Game-Types (Q Resp : Type){Λ : Type}(Prf : Λ → Type) where
  Random-Oracle : Type
  Random-Oracle = Q → Resp

  data Adversary-Query : Type where
    query-H : (q : Q) → Adversary-Query
    query-create-proof : (w : W)(Y : Λ) → Adversary-Query

  Challenger-Resp : Adversary-Query → Type
  Challenger-Resp (query-H s) = Resp
  Challenger-Resp (query-create-proof w Y) = Maybe (Prf Y)

  Adversary : Type → Type
  Adversary = Strategy Adversary-Query Challenger-Resp

  Transcript = List (Σ Adversary-Query Challenger-Resp)

  Prfs : Type
  Prfs = List (Σ Λ Prf)

  Res = Σ Λ Prf

  module With-Prf? (Prf? : ∀ {Y Y'} → Prf Y → Prf Y' → 𝟚) where
    Prf-in-Q : ∀ {Y} → Prf Y → Σ Adversary-Query Challenger-Resp → 𝟚
    Prf-in-Q π (query-create-proof _ _ , just π') = Prf? π π'
    Prf-in-Q π _                                  = 0₂


    module Prf-Transcript (Verify : (Y : Λ)(π : Prf Y) → 𝟚) (t : Transcript) where

        Prf-in-Transcript : ∀ {Y} → Prf Y → 𝟚
        Prf-in-Transcript π = any (Prf-in-Q π) t

        K-winning-prf : Σ Λ Prf → 𝟚
        K-winning-prf (Y , π) = not (Verify Y π)
                              ∨ Prf-in-Transcript π

        K-winning-prfs : Prfs → 𝟚
        K-winning-prfs []   = 1₂
        K-winning-prfs prfs = any K-winning-prf prfs

record Simulator (Q : Type)(Resp : Type){Prf RP}(PF : Proof-System RP Prf) : Type where
  open Proof-System PF
  open Game-Types Q Resp Prf

  field
    -- Computing the compound patch to the random oracle
    H-patch  : RS → Transcript → Random-Oracle → Random-Oracle

    -- Simulate does not patch itself but H-patch does
    Simulate : RS → Transcript → (Y : Λ) → Prf Y
    verify-sim-spec : ∀ rs t Y → Verify Y (Simulate rs t Y) ≡ 1₂

  open Proof-System PF public
  open Game-Types Q Resp Prf public

module Is-Zero-Knowledge
  {RP Prf Q Resp}
  (L-to-Prf : ∀ {w Y} → L w Y → Prf Y)
  (PF : Proof-System RP Prf)
  (open Proof-System PF)
  (sim : Simulator Q Resp PF)
  (open Simulator sim)
  (ro : Random-Oracle)
  where

    simulated-Challenger : RS → Transcript → ∀ q → Challenger-Resp q
    simulated-Challenger rs t (query-H q) = H-patch rs t ro q
    simulated-Challenger rs t (query-create-proof w Y) with L? w Y
    ... | yes p = just (Simulate rs t Y)
    ... | no ¬p = nothing

    real-Challenger : ∀ q → Challenger-Resp q
    real-Challenger (query-H q) = ro q
    real-Challenger (query-create-proof w Y) with L? w Y
    ... | yes p = just (L-to-Prf p)
    ... | no  _ = nothing

    challenger : 𝟚 → RS → Transcript → ∀ q → Challenger-Resp q
    challenger 0₂ _  _ = real-Challenger
    challenger 1₂ rs t = simulated-Challenger rs t

    open TranscriptRun
    -- β = 0₂ is real
    -- β = 1₂ is simulated
    Experiment : ∀ {Output} → 𝟚 → Adversary Output → RS → Output × Transcript
    Experiment β adv rs = runT (challenger β rs) adv []

    EXP₀ EXP₁ : Adversary 𝟚 → RS → 𝟚
    EXP₀ Adv = fst ∘ Experiment 0₂ Adv
    EXP₁ Adv = fst ∘ Experiment 1₂ Adv

    -- Too strong
    IsZK = ∀ Adv → EXP₀ Adv ≈ EXP₁ Adv

{-
-- there exists a simulator, such that for all adversaries they are clueless if
-- they are in the real or simulated Experiment
Zero-Knowledge : Proof-System → Type
Zero-Knowledge PF = Σ (Simulator PF) (λ sim → {!!})
-}

module Simulation-Sound-Extractability
           {RP}{Prf : Λ → Type}
           (PF : Proof-System RP Prf)
           (Prf? : ∀ {Y Y'} → Prf Y → Prf Y' → 𝟚)
           (Q Resp E-State : Type)
           where
    open Proof-System PF
    open Game-Types Q Resp Prf
    open With-Prf? Prf?
    open Prf-Transcript Verify

    HistoryForExtractor = List (Prfs × Transcript)

    ExtractorServerPart =
         (state : E-State)                    {- The current query -}
         (past-history : HistoryForExtractor) {- previous invocations of Adv -}
         (on-going-transcript : Transcript)   {- about the current invocation of Adv -}
       → Π Adversary-Query Challenger-Resp

    Extractor : Type
    Extractor = Prfs → (init-transcript : Transcript)
                     → ExtractorServerPart
                     × Strategy E-State (const (Prfs × Transcript)) (List W)

    {-
    wip : Extractor → Σ Λ Prf → {!!} → W
    wip K Yπ = {!K (Yπ ∷ [])!}
    -}

    open TranscriptRun

    module Game
        (L-to-Prf : ∀ {w Y} → L w Y → Prf Y)
        (sim : Simulator Q Resp PF)
        (open Is-Zero-Knowledge L-to-Prf PF sim)
        {RA : Type}

        {- The malicious prover -}
        (Adv : RA → Adversary Prfs)
        (w : RA)(rs : RS)(ro : Q → Resp)(K' : Extractor) where

        initial-result = Experiment ro 1₂ (Adv w) rs

        initial-prfs : Prfs
        initial-prfs = fst initial-result

        initial-transcript : Transcript
        initial-transcript = snd initial-result

        K-winning-initial-run : 𝟚
        K-winning-initial-run = K-winning-prfs initial-transcript initial-prfs

        -- Second run

        K = K' initial-prfs initial-transcript

        Kf = fst K
        Ks = snd K

        ws = fst (runT (λ h e-s → runT (λ t q → Kf e-s (mapᴸ snd h) t q) (Adv w) []) Ks [])

        K-winning-second-run : 𝟚
        K-winning-second-run = valid-witnesses? ws (mapᴸ fst initial-prfs)

module Simulation-Sound-Extractability-Unary-Forced
           {RP}{Prf : Λ → Type}
           (PF : Proof-System RP Prf)
           (Prf? : ∀ {Y Y'} → Prf Y → Prf Y' → 𝟚)
           (Q Resp : Type)
           (Y : Λ)
           where
    open Proof-System PF
    open Game-Types Q Resp Prf public hiding (Prfs)
    open With-Prf? Prf?
    open Prf-Transcript Verify

    ExtractorServerPart : Type
    ExtractorServerPart =
         (on-going-transcript : Transcript)   {- about the current invocation of Adv -}
       → Π Adversary-Query Challenger-Resp

    Extractor : Type
    Extractor = Prf Y → (init-transcript : Transcript) → ExtractorServerPart × ((Prf Y × Transcript) → W)

    module Game
        (L-to-Prf : ∀ {w Y} → L w Y → Prf Y)
        (sim : Simulator Q Resp PF)
        (open Is-Zero-Knowledge L-to-Prf PF sim)
        {RA : Type}

        {- The malicious prover -}
        (Adv : RA → Adversary (Prf Y))
        (ω : RA)(rs : RS)(ro : Q → Resp)(K' : Extractor) where

        initial-result = Experiment ro 1₂ (Adv ω) rs

        initial-transcript : Transcript
        initial-transcript = snd initial-result

        K-winning-intial-run : 𝟚
        K-winning-intial-run = K-winning-prf (snd initial-result) (Y , fst initial-result)

        -- Second run

        K = uncurry K' initial-result

        Kf = fst K
        Ks = snd K

        open TranscriptRun
        w : W
        w = Ks (runT Kf (Adv ω) [])

        K-winning-second-run : 𝟚
        K-winning-second-run = valid-witness? w Y

-- This module changes the game from the paper to be simpler to understand
-- this is done purely for educational reasons, we make no claim about the security implications
module Simulation-Sound-Extractability-[EXPERIMENTAL]
           {RP}{Prf : Λ → Type}
           (PF : Proof-System RP Prf)
           (Prf? : ∀ {Y Y'} → Prf Y → Prf Y' → 𝟚)
           (Q Resp : Type)
           where
    open Proof-System PF
    open Game-Types Q Resp Prf public hiding (Prfs)
    open With-Prf? Prf?
    open Prf-Transcript Verify

    ExtractorServerPart : Type
    ExtractorServerPart =
         (on-going-transcript : Transcript)   {- about the current invocation of Adv -}
       → Π Adversary-Query Challenger-Resp

    Extractor : Type
    Extractor = Res → (init-transcript : Transcript) → ExtractorServerPart × ((Res × Transcript) → W)

    module Game
        (L-to-Prf : ∀ {w Y} → L w Y → Prf Y)
        (sim : Simulator Q Resp PF)
        (open Is-Zero-Knowledge L-to-Prf PF sim)
        {RA : Type}

        {- The malicious prover -}
        (Adv : RA → Adversary Res)
        (ω : RA)(rs : RS)(ro : Q → Resp)(K' : Extractor) where

        initial-result = Experiment ro 1₂ (Adv ω) rs

        K-winning-intial-run : 𝟚
        K-winning-intial-run = K-winning-prf (snd initial-result) (fst initial-result)

        -- Second run

        K = uncurry K' initial-result

        Kf = fst K
        Ks = snd K

        open TranscriptRun
        w : W
        w = Ks (runT Kf (Adv ω) [])

        K-winning-second-run : 𝟚
        K-winning-second-run = valid-witness? w (fst (fst initial-result))

module Lift-to-list
           {RP}{Prf : Λ → Type}
           (PF : Proof-System RP Prf)
           (Prf? : ∀ {Y Y'} → Prf Y → Prf Y' → 𝟚)
           (Q Resp : Type)
  where

  E-State : Type
  E-State = Σ Λ Prf

  open Game-Types Q Resp Prf
  module Unary  = Simulation-Sound-Extractability-[EXPERIMENTAL] PF Prf? Q Resp
  module Lifted = Simulation-Sound-Extractability                PF Prf? Q Resp E-State
  open RepeatIndex

  lookup : {A : Set} → ℕ → List A → Maybe A
  lookup n [] = nothing
  lookup zero (x ∷ xs) = just x
  lookup (suc n) (x ∷ xs) = lookup n xs

  trans-server : Unary.Extractor → Transcript → Lifted.ExtractorServerPart
  trans-server K sim-tran Σπ _ this-tran q = fst (K Σπ sim-tran) this-tran q

  trans-strat : Unary.Extractor → List Unary.Res → Transcript → Strategy E-State (const (Prfs × Transcript)) (List W)
  trans-strat K xs tran = map-list (λ { i Σπ (p , t) → snd (K Σπ tran) (maybe′ id Σπ (lookup i p) , t)}) xs
  {-
  trans-strat K []         tran = done []
  trans-strat K (Σπ ∷ res) tran = ask Σπ (λ { (p , t) → let w = snd (K Σπ tran) ({!p!} , t) in mapS (_∷_ w) (trans-strat K res tran) } )
  -}

  transformation : Unary.Extractor → Lifted.Extractor
  transformation K res tran = trans-server K tran , trans-strat K res tran

  module Game
      (L-to-Prf : ∀ {w Y} → L w Y → Prf Y)
      (sim : Simulator Q Resp PF)
      (open Is-Zero-Knowledge L-to-Prf PF sim)
      {RA : Type}

      {- The malicious prover -}
      (Adv : RA → Adversary Prfs)
      (ω : RA)(rs : RS)(ro : Q → Resp)(K' : Unary.Extractor) where

      module LGame = Lifted.Game L-to-Prf sim Adv ω rs ro (transformation K')
      open TranscriptRun
      open ≡-Reasoning


      Oracle : E-State → Prfs × Transcript
      Oracle e-s = runT (LGame.Kf e-s []) (Adv ω) []

      ws' : List W
      ws' = run Oracle LGame.Ks

      {-
      ws'-correct : LGame.ws ≡ {!!}
      ws'-correct =
         LGame.ws
        ≡⟨ TranscriptConstRun.runT-run _ LGame.Ks ⟩
          run Oracle LGame.Ks
        ≡⟨ run-map-list Oracle LGame.initial-prfs _ ⟩
          mapIndex
            (λ i q →
               let (p , t) = Oracle q
                in snd (K' q LGame.initial-transcript)
                       (maybe′ id q (lookup i p) , t))
            LGame.initial-prfs
        ≡⟨ {!!} ⟩
          {!!}
        ∎
      -}

      thm : LGame.K-winning-initial-run ≡ 0₂ → LGame.K-winning-second-run ≡ 1₂
      thm eq = {!λ e → LGame.Kf e []!}

module Sigma-Protocol
  (Commitment Challenge : Type)
  (Σ-Prf : Λ → Type)
  {RΣP : Type}
  (any-RΣP : RΣP)
  where

  record Σ-Prover : Type where
    field
      get-A : RΣP → (Y : Λ) → Commitment
      get-f : RΣP → (Y : Λ) → (c : Challenge) → Σ-Prf Y

  record Σ-Transcript (Y : Λ) : Type where
    constructor mk
    field
      get-A : Commitment
      get-c : Challenge
      get-f : Σ-Prf Y

  Σ-Verifier : Type
  Σ-Verifier = (Y : Λ)(t : Σ-Transcript Y) → 𝟚

  record Σ-Protocol : Type where
    constructor _,_
    field
      Σ-verifier : Σ-Verifier
      Σ-prover   : Σ-Prover
    open Σ-Prover Σ-prover public

    Σ-game : (r : RΣP)(rc : Challenge)(Y : Λ) → 𝟚
    Σ-game r rc Y = Σ-verifier Y (mk A rc f)
      where
        A = get-A r Y
        f = get-f r Y rc

  _⇄_ : Σ-Verifier → Σ-Prover → RΣP → Λ → Challenge → 𝟚
  (v ⇄ p) r Y rc = Σ-Protocol.Σ-game (v , p) r rc Y

  Correct : Σ-Protocol → Type
  Correct p = ∀ {Y w} → L w Y → (r : RΣP)(c : _) →
    let open Σ-Protocol p
    in Σ-game r c Y ≡ 1₂

  record Special-Honest-Verifier-Zero-Knowledge (Σ-proto : Σ-Protocol) : Type where
    open Σ-Protocol Σ-proto
    field
      Simulate : (Y : Λ)(c : Challenge)(f : Σ-Prf Y) → Commitment
      Simulate-ok : ∀ Y c f → Σ-verifier Y (mk (Simulate Y c f) c f) ≡ 1₂
      -- If (c,f) uniformly distributed then (Simulate Y c f , c , f) is
      -- distributed equaly to ((Σ-verifier ⇄ Σ-prover) r Y c)

  -- A pair of "Σ-Transcript"s such that the commitment is shared
  -- and the challenges are different.
  record Σ-Transcript² Σ-proto (Y : Λ) : Type where
    constructor mk
    open Σ-Protocol Σ-proto using (Σ-verifier)
    field
      -- The commitment is shared
      get-A         : Commitment

      -- The challenges...
      get-c₀ get-c₁ : Challenge

      -- ...are different
      c₀≢c₁         : get-c₀ ≢ get-c₁

      -- The proofs are arbitrary
      get-f₀ get-f₁ : Σ-Prf Y

    -- The two transcripts
    t₀ : Σ-Transcript Y
    t₀ = mk get-A get-c₀ get-f₀
    t₁ : Σ-Transcript Y
    t₁ = mk get-A get-c₁ get-f₁

    field
      -- The Σ-transcripts verify
      verify₀ : Σ-verifier Y t₀ ≡ 1₂
      verify₁ : Σ-verifier Y t₁ ≡ 1₂

  record Special-Soundness Σ-proto : Type where
    field
      Extract    : ∀ {Y}(t : Σ-Transcript² Σ-proto Y) → W
      Extract-ok : ∀ {Y}(t : Σ-Transcript² Σ-proto Y) → L (Extract t) Y

  module Fiat-Shamir-Transformation
              (Σ-proto : Σ-Protocol)
              -- For the transformation we technically only need Simulate, no proofs...
              -- but we take the proofs as well
              (shvzk : Special-Honest-Verifier-Zero-Knowledge Σ-proto)
              where

      open Σ-Protocol Σ-proto
      open Special-Honest-Verifier-Zero-Knowledge shvzk

      FS-Prf : Λ → Type
      FS-Prf Y = Challenge × Σ-Prf Y

      sFS : (H : (Λ × Commitment) → Challenge) → Proof-System RΣP FS-Prf
      sFS H = record { Prove = sFS-Prove ; Verify = sFS-Verify }
        where
          sFS-Prove : RΣP → W → (Y : Λ) → FS-Prf Y
          sFS-Prove r w Y = let c = H (Y , get-A r Y) in c , get-f r Y c
          sFS-Verify : ∀ Y → FS-Prf Y → 𝟚
          sFS-Verify Y (c , π) = Σ-verifier Y (mk (Simulate Y c π) c π)

      -- The weak fiat-shamir is like the strong one but the H function do not get to see
      -- the statement, hence the 'snd'
      wFS : (H : Commitment → Challenge) → Proof-System RΣP (λ Y → Challenge × Σ-Prf Y)
      wFS H = sFS (H ∘ snd)

  module Theorem1
              (Σ-proto : Σ-Protocol)
              -- (Σ-correct : Correct Σ-proto)
              (shvzk   : Special-Honest-Verifier-Zero-Knowledge Σ-proto)
              (ssound  : Special-Soundness Σ-proto)
              (open Σ-Protocol Σ-proto)
              (H : (Λ × Commitment) → Challenge)
              where
      module SHVZK = Special-Honest-Verifier-Zero-Knowledge shvzk

      module FST = Fiat-Shamir-Transformation Σ-proto shvzk
      open FST using (FS-Prf)

      Q = Λ × Commitment
      Resp = Challenge

      sFS : Proof-System RΣP FS-Prf
      sFS = FST.sFS H
      module SFS = Proof-System sFS

      FS-Prf? : {Y Y' : Λ} → FS-Prf Y → FS-Prf Y' → 𝟚
      FS-Prf? π π' = {!!}

      E-State : Type
      E-State = 𝟙

      open Simulation-Sound-Extractability sFS FS-Prf? Q Resp E-State

      L-to-FS-Prf : ∀ {w Y} → L w Y → FS-Prf Y
      L-to-FS-Prf {w} w∈Y = SFS.Prove any-RΣP w _

      FS-Random-Oracle = (Λ × Commitment) → Challenge
      FS-Patch = FS-Random-Oracle → FS-Random-Oracle

      open Special-Soundness ssound
      open Game-Types Q Resp FS-Prf

      module _ (rnd-c : Λ → Challenge)(rnd-Σ-Prf : ∀ Y → Σ-Prf Y) where

        module _ (rs : RS) where
        {-
          Σ-t² : ∀{Y} → SFS.Transcript → Maybe (Σ-Transcript² Y)
          Σ-t² t = {!!}
          -}


    {-
module H-def (ro : Random-Oracle)(t : Random-Oracle-List)(q : Q) where
  H : Resp
  H with find (λ { (query-H q' , r) → ⌊ Q? q' q ⌋
                 ; (query-create-proof _ _ , _) → 0₂ }) t
  ... | just (query-H q₁ , r) = r
  ... | _ = ro q
  -}
          H-patch-1 : (q : Adversary-Query) → Challenger-Resp q → FS-Random-Oracle → FS-Random-Oracle
          H-patch-1 (query-H q) r = id
          H-patch-1 (query-create-proof w Y) r ro (Y' , c')
            = ro (Y' , case ⌊ Λ? Y Y' ⌋ 0: c' 1: SHVZK.Simulate Y (rnd-c Y) (rnd-Σ-Prf Y))

          H-patch : Transcript → FS-Patch
          H-patch []            = id
          H-patch ((q , r) ∷ t) = H-patch-1 q r ∘ H-patch t

          module _ (t : Transcript)(Y : Λ) where
              Simulate : FS-Prf Y
              Simulate = rnd-c Y , rnd-Σ-Prf Y
              -- SFS.Prove any-RΣP (maybe′ (Extract {Y}) any-W (Σ-t² t)) Y

              c : Challenge
              c = fst Simulate

              Σ-prf : Σ-Prf Y
              Σ-prf = snd Simulate

              verify-sim-spec : SFS.Verify Y Simulate ≡ 1₂
              verify-sim-spec = SHVZK.Simulate-ok Y c Σ-prf

        S : Simulator (Λ × Commitment) Challenge sFS
        S = record { H-patch = H-patch
                   ; Simulate = Simulate
                   ; verify-sim-spec = verify-sim-spec }

        open Is-Zero-Knowledge L-to-FS-Prf sFS S {!!}

        K0 : Prfs → Transcript → ExtractorServerPart
        K0 prfs init-transcript past-history on-going-transcript q = {!!}

        K1 : Prfs → Transcript → Strategy 𝟙 (const (Prfs × Transcript)) (List W)
        K1 [] init-transcript = done {!!}
        K1 ((Y , π) ∷ prfs) init-transcript = ask _ (λ pt → {!!})

        K : Extractor
        K prfs init-transcript = K0 prfs init-transcript , K1 prfs init-transcript

        module _ Adv where
          is-zk' : EXP₀ Adv ≋ EXP₁ Adv
          is-zk' = {!!}

        is-zk : IsZK
        is-zk Adv = ≋→≈ (is-zk' Adv)

-- -}
-- -}
-- -}
-- -}
-- -}
